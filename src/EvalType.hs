-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalType :: Program -> Maybe Type 就行。
module EvalType where

import AST
import Control.Monad.State
import qualified Data.Map.Strict as M

data Context = Context { variableMap :: M.Map String Type,
                          constructorTypeMap :: M.Map String Type,
                          constructors :: M.Map String [Type]  -- 可以用某种方式定义上下文，用于记录变量绑定状态
                       }
  deriving (Show, Eq)

type ContextState a = StateT Context Maybe a

-- check if the type of the expression is bool or not
isBool :: Expr -> ContextState Type
isBool e = do
  et <- eval e
  case et of
    TBool -> return TBool
    _ -> lift Nothing

-- check if the type of the expression is int or not
isInt :: Expr -> ContextState Type
isInt e = do
  et <- eval e
  case et of
    TInt -> return TInt
    _ -> lift Nothing
    

-- check if expr1 and expr2 have the same type
sameType :: Expr -> Expr ->ContextState Type
sameType e1 e2 = do
  e1type <- eval e1
  e2type <- eval e2
  if e1type == e2type
  then return e1type
  else lift Nothing

equalable :: Expr -> ContextState Type
equalable e = do
  et <- eval e
  case et of
    TInt -> return TInt
    TBool -> return TBool
    TChar -> return TChar
    _ -> lift  Nothing


-- check if the type of the expression is comparable
comparable :: Expr -> ContextState Type
comparable e = do
  et <- eval e
  case et of 
    TInt -> return TInt
    TChar -> return TChar
    _ -> lift  Nothing


-- operation with local variable
withVar :: String -> Type -> ContextState Type -> ContextState Type
withVar x t op = do
  -- push local variable
  ctx <- get
  put (Context  (M.insert x t (variableMap ctx))  (constructorTypeMap ctx) (constructors ctx) )

  -- do the operation
  result <- op

  -- pop local variable out
  put ctx
  return result 


-- operation with local function 
withFunc :: String -> Type -> Type -> ContextState Type -> ContextState Type
withFunc x t1 t2 op = do
  ctx <- get
  put (Context (M.insert x (TArrow t1 t2) (variableMap ctx))   (constructorTypeMap ctx) (constructors ctx) )

  result <- op

  put ctx
  return result

checkFuncRetType :: String -> String -> Type -> Expr -> Type -> ContextState Type
checkFuncRetType funcName vName vt expr rt = do
  ctx <- get
  put $ (Context (M.insert funcName (TArrow vt rt) (variableMap ctx))   (constructorTypeMap ctx) (constructors ctx) )
  et <- withVar vName vt (eval expr)
  put ctx
  case et == rt of
    True -> return $ TArrow vt rt
    False -> lift  Nothing

checkFuncApply :: Type -> Type ->ContextState Type
checkFuncApply vt (TArrow t1 t2) = case vt == t1 of
  True -> return t2
  False -> lift  Nothing

patternTypeEqual :: Pattern -> Type -> ContextState Bool
patternTypeEqual p1 t =
  case p1 of 
    PBoolLit b -> return (TBool == t)
    PIntLit i -> return (TInt == t)
    PCharLit c -> return (TChar == t)
    PVar s -> return True
    PData string ps -> constructorPatternValid (PData string ps)

caseTypeEqual :: [Pattern] -> Type -> ContextState Bool
caseTypeEqual (p:ps) t = do
  b <- patternTypeEqual p t
  bs <- caseTypeEqual ps t
  return b && bs
caseTypeEqual [] t = return True


patternsTypeEqual :: [Pattern] -> [Type] -> Bool -> ContextState Bool
patternsTypeEqual (p:ps) (t:ts) acc= do
  eq <- (patternTypeEqual p t)
  patternsTypeEqual ps ts (eq && acc)
patternsTypeEqual [] [] acc = return acc

constructorPatternValid :: Pattern -> ContextState Bool
constructorPatternValid (PData string ps) = do
  ctx <- get
  case ((constructors ctx) M.!? string) of
    Just ts -> case (length ts /= length ps) of
      False -> (patternsTypeEqual ps ts True)
      _ -> return False
    _ -> return False



reTypeEqual :: [(Pattern,Expr)] -> Type -> ContextState Type
reTypeEqual ((pt,expr):ps) ptType = do
  case pt of
    PVar nName -> do
      et <- withVar nName ptType (eval expr)
      return et
    PData dName ps -> do
      
eval :: Expr -> ContextState Type
eval (EBoolLit _) = return TBool
eval (EIntLit _) = return TInt
eval (ECharLit _) = return TChar

eval (ENot e) = isBool e >> return TBool
eval (EAnd e1 e2) = isBool e1 >> isBool e2 >> return TBool
eval (EOr e1 e2) = isBool e1 >> isBool e2 >> return TBool

eval (EAdd e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (ESub e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EMul e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EDiv e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EMod e1 e2) = isInt e1 >> isInt e2 >> return TInt

eval (EEq e1 e2) = equalable e1 >> equalable e2 >> sameType e1 e2 >> return TBool
eval (ENeq e1 e2) = equalable e1 >> equalable e2 >> sameType e1 e2 >> return TBool
eval (ELt e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (EGt e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (ELe e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (EGe e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool

eval (EIf e1 e2 e3) = isBool e1 >> sameType e2 e3 >> do 
  et <- eval e2
  return et

eval (ELambda (vName,vt) e) = do
  et <- withVar vName vt (eval e)
  return $ TArrow vt et

eval (EVar vName) = do
  ctx <- get
  case ((variableMap ctx) M.!? vName) of 
    Nothing -> lift Nothing
    Just t -> return t

eval (ELet (vName, e1) e2) = do
  e1t <- eval e1
  e <- withVar vName e1t (eval e2)
  return e

eval (ELetRec funcName (vName ,vt) (e1,et1) e2) = do
  ft <- checkFuncRetType funcName vName vt e1 et1
  et <- withVar funcName ft (eval e2)
  -- -- ft <- checkFuncRetType vName vt e1 et1
  -- et <- withVar funcName (TArrow vt et1) (eval e2)
  return et

eval (EApply e1 e2) = do
  ft <- eval e1
  vt <- eval e2
  case ft of 
    (TArrow t1 t2) -> checkFuncApply vt ft
    _ -> lift Nothing

eval (ECase expr ps) = do
  et <- eval expr
  pcheck <- caseTypeEqual (fst $ unzip ps) et
  case pcheck of
    False -> lift Nothing
    _ -> do 
      echeck <- reTypeEqual ps
eval _ = undefined


evalType :: Program -> Maybe Type
evalType (Program adts body) = evalStateT (eval body) $
  (Context (M.fromList []) (M.fromList (constructorTypesFromADTs adts)) (M.fromList (constructorContentFromADTs adts))) -- 可以用某种方式定义上下文，用于记录变量绑定状态


constructorTypesFromADT (ADT name ax) = foldl (\acc x-> (x,TData name) : acc) [] (fst $ unzip ax)
constructorTypesFromADTs adts = foldl (\acc x -> (constructorTypesFromADT x) ++ acc) [] adts

constructorContentFromADT (ADT name ax) = ax
constructorContentFromADTs adts = foldl (\acc x -> (constructorContentFromADT x) ++ acc) [] adts

simpleEvalExpr expr = evalType (Program [] expr)