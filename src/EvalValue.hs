-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalValue :: Program -> Result 就行。
module EvalValue where

import AST
import Control.Monad.State
import qualified Data.Map.Strict as M

data Value
  = VBool Bool
  | VInt Int
  | VChar Char
  | VFunc Expr
  -- ... more
  deriving (Show, Eq)

data Context = Context { variableMap :: M.Map String Value,fp::Maybe Expr-- 可以用某种方式定义上下文，用于记录变量绑定状态
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

vCompareChar op (VInt v1) (VInt v2)  = return $ VBool (op v1 v2)


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
    

eval _ = undefined

evalProgram :: Program -> Maybe Value
evalProgram (Program adts body) = evalStateT (eval body) $
  Context (M.fromList []) Nothing  -- 可以用某种方式定义上下文，用于记录变量绑定状态


evalValue :: Program -> Result
evalValue p = case evalProgram p of
  Just (VBool b) -> RBool b
  Just (VInt i) -> RInt i
  Just (VChar c) -> RChar c
  _ -> RInvalid

simpleValue expr = evalProgram (Program [] expr)