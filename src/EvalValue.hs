-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalValue :: Program -> Result 就行。
module EvalValue where

import AST
import Control.Monad.State
import qualified Data.Map.Strict as M

data Value
  = VBool Bool
  | VInt Int
  | VChar Char
  | VExpr Expr [(String,Value)]
  | VData String [Value]
  -- ... more
  deriving (Show, Eq)

data Context = Context { variableMap :: M.Map String Value,
                         fp::Maybe Value,
                         constructorFuncMap :: M.Map String Value
                         -- 可以用某种方式定义上下文，用于记录变量绑定状态
                          } deriving (Show, Eq)

type ContextState a = StateT Context Maybe a

getBool :: Expr -> ContextState Bool
getBool e = do
  ev <- eval e
  case ev of
    VBool b -> return b
    _ -> lift Nothing


-- vCompare :: Ord a => ( a -> a-> Bool)-> Value -> Value -> ContextState Value
-- vCompare op (VInt v1) (VInt v2)  = return $ VBool (op v1 v2)
-- vCompare op (VChar c1) (VChar c2) = return $ VBool (op c1 c2)

vCompareInt :: ( Int -> Int-> Bool)-> Value -> Value -> ContextState Value
vCompareInt op (VInt v1) (VInt v2)  = return $ VBool (op v1 v2)

vCompareChar op (VChar v1) (VChar v2)  = return $ VBool (op v1 v2)

withVar :: String -> Value -> ContextState Value -> ContextState Value
withVar n v op = do
  -- push local variable
  ctx <- get
  put (Context (M.insert n v (variableMap ctx)) (fp ctx) (constructorFuncMap ctx))
  -- do the operation
  result <- op
  -- pop local variable out
  put ctx
  return result

withVars :: [(String,Value)] -> ContextState Value -> ContextState Value
withVars ((name,value):xs) op = 
  withVar name value (withVars xs op)
withVars [] op = do
  result <- op
  return result

withFP :: Value -> ContextState Value -> ContextState Value
withFP v op = do
  ctx <- get
  put (Context (variableMap ctx) (Just v) (constructorFuncMap ctx) )
  result <- op
  put ctx
  return result

getFP :: ContextState Value
getFP = do
  ctx <- get
  case fp ctx of
    Just value -> 
      put (Context (variableMap ctx) Nothing (constructorFuncMap ctx)) >>
      return value
    _ -> lift Nothing

eval :: Expr -> ContextState Value
eval (EBoolLit b) = return $ VBool b
eval (ENot e) = getBool e >>= \b -> return (VBool $ not b)
eval (EIntLit i) = return $ VInt i
eval (ECharLit c) = return $ VChar c

eval (EAnd e1 e2) = do
  (VBool v1) <- eval e1
  case v1 of
    False -> return $ VBool False
    _ ->do
      (VBool v2) <- eval e2
      return $ VBool (v2 && v1)

eval (EOr e1 e2) = do
  (VBool v1) <- eval e1
  case v1 of
    True -> return $ VBool True
    _ ->do
      (VBool v2) <- eval e2
      return $ VBool (v2 || v1)

eval (EAdd e1 e2) = do
  (VInt v1) <- eval e1
  (VInt v2) <- eval e2
  return $ VInt (v1 + v2)


eval (ESub e1 e2) = do 
  (VInt v1) <- eval e1
  (VInt v2) <- eval e2
  return $ VInt (v1 - v2)

eval (EMul e1 e2) = do 
  (VInt v1) <- eval e1
  (VInt v2) <- eval e2
  return $ VInt (v1 * v2)

eval (EDiv e1 e2) = do 
  (VInt v1) <- eval e1
  (VInt v2) <- eval e2
  case v2 of
    0 -> lift Nothing
    _ -> return $ VInt (div v1 v2)

eval (EMod e1 e2) = do 
  (VInt v1) <- eval e1
  (VInt v2) <- eval e2
  case v2 of
    0 -> lift Nothing
    _ -> return $ VInt (mod v1 v2)
  -- ... more

eval (EEq e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  return $ VBool (v1 == v2)

eval (ENeq e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  return $ VBool (v1 /= v2)

eval (ELt e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
    (VInt v) -> vCompareInt (<) v1 v2
    _ -> vCompareChar (<) v1 v2
    -- _ -> vCompareChar (<) v1 v2

eval (EGt e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
    (VInt v) -> vCompareInt (>) v1 v2
    _ -> vCompareChar (>) v1 v2

eval (ELe e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
    (VInt v) -> vCompareInt (<=) v1 v2
    _ -> vCompareChar (<=) v1 v2


eval (EGe e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
    (VInt v) -> vCompareInt (>=) v1 v2
    _ -> vCompareChar (>=) v1 v2

  

eval (EIf e1 e2 e3) = do
  condition <- eval e1
  case condition of
    (VBool True) -> eval e2
    (VBool False) -> eval e3
    _ -> lift Nothing
    
eval (ELambda (vName,vt) e) = do
  ctx <- get
  case (fp ctx) of
    Nothing -> do
      return (VExpr (ELambda (vName,vt) e) [])
    Just value -> do
      v <- getFP
      re <- withVar vName v (eval e)
      case re of
        VExpr expr acc -> return (VExpr expr ((vName,value):acc))
        _ -> return re


eval (ELet (vName,vexpr) expr) = do
  variabelValue <- eval vexpr
  re <- withVar vName variabelValue (eval expr)
  return re

eval (ELetRec funcName (v , vt) (fexpr , ft) expr) = do
  func <- eval (ELambda (v,vt) fexpr)
  re <- withVar funcName func (eval expr)
  return re

eval (EVar vName) = do
  ctx <- get
  case ((variableMap ctx) M.!? vName) of 
    Nothing -> lift Nothing
    Just v -> return v

eval (EApply e1 e2) = do
  VExpr expr locals <- eval e1
  v <- eval e2
  result <- withVars locals (withFP v (eval expr) )
  case result of
    VExpr expr newlocals -> return (VExpr expr (locals ++ newlocals))
    _ -> return result


eval (ECase expr pes) = do
  ev <- eval expr
  result <- evalMatchPattern ev pes
  return result

  
eval (EData cons es) = do
  esv <- evalExprs es
  return (VData cons esv)

patternEqual :: Value -> Pattern -> ContextState Bool
patternEqual (VData vcons vs) (PData pcons ps) = do
  case vcons == pcons of 
    True -> do
      vsEqual <- patternsEqual vs ps
      return vsEqual
    False -> return False
patternEqual _ (PVar vName) = do
  return True
patternEqual (VInt vv) (PIntLit pv) = do
  return $ vv == pv
patternEqual (VBool vv) (PBoolLit pv) = do
  return $ vv == pv
patternEqual (VChar vv) (PCharLit pv) = do
  return $ vv == pv
patternEqual _ _  = do
  return False

patternsEqual :: [Value] -> [Pattern] -> ContextState Bool
patternsEqual (v:vs) (p:ps)  = do
  vv <- patternEqual v p
  vsv <- patternsEqual vs ps
  return (vv && vsv)
patternsEqual [] [] = do
  return True


evalMatchPattern :: Value -> [(Pattern,Expr)] -> ContextState Value
evalMatchPattern v ((p,e):pes) = do
  pm <- patternEqual v p
  case pm of
    False -> evalMatchPattern v pes
    True -> evalInPattern v p (eval e)
evalMatchPattern _ [] = do
  lift Nothing
  
evalInPattern :: Value -> Pattern -> ContextState Value -> ContextState Value
evalInPattern v (PVar name) op  = do
  vv <- withVar name v op
  return vv
evalInPattern (VData vcons vs) (PData pcons ps) op= do
  vv <- evalInPatterns vs ps op
  return vv
evalInPattern v _ op = op

evalInPatterns :: [Value] -> [Pattern] -> ContextState Value -> ContextState Value
evalInPatterns (v:vs) (p:ps) op = do
  vv <- evalInPattern v p (evalInPatterns vs ps op)
  return vv
evalInPatterns [] [] op = do
  vv <- op
  return vv


evalExprs :: [Expr] -> ContextState [Value]
evalExprs (e:es) = do
  ev <- eval e
  esv <- evalExprs es
  return (ev:esv)
evalExprs [] = do
  return []

evalProgram :: Program -> Maybe Value
evalProgram (Program adts body) = evalStateT (eval body) $
  Context (M.fromList []) Nothing (M.fromList []) -- 可以用某种方式定义上下文，用于记录变量绑定状态


evalValue :: Program -> Result
evalValue p = case evalProgram p of
  Just (VBool b) -> RBool b
  Just (VInt i) -> RInt i
  Just (VChar c) -> RChar c
  _ -> RInvalid

simpleValue expr = evalProgram (Program [] expr)