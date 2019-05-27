-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalType :: Program -> Maybe Type 就行。
module EvalType where

import AST
import Control.Monad.State
import qualified Data.Map.Strict as M

data Context = Context { variableMap :: M.Map String Type -- 可以用某种方式定义上下文，用于记录变量绑定状态
                       }
  deriving (Show, Eq)

type ContextState a = StateT Context (Either String) a

-- check if the type of the expression is bool or not
isBool :: Expr -> ContextState Type
isBool e = do
  et <- eval e
  case et of
    TBool -> return TBool
    _ -> lift $ Left "not bool"

-- check if the type of the expression is int or not
isInt :: Expr -> ContextState Type
isInt e = do
  et <- eval e
  case et of
    TInt -> return TInt
    _ -> lift $ Left "not int"
    

-- check if expr1 and expr2 have the same type
sameType :: Expr -> Expr ->ContextState Type
sameType e1 e2 = do
  e1type <- eval e1
  e2type <- eval e2
  if e1type == e2type
  then return e1type
  else lift $ Left "different type in comparing"


-- check if the type of the expression is comparable
comparable :: Expr -> ContextState Type
comparable e = do
  et <- eval e
  case et of 
    TInt -> return TInt
    TBool -> return TBool
    TChar -> return TChar
    _ -> lift $ Left "not comparable"


-- operation with local variable out
withVar :: String -> Type -> ContextState Type -> ContextState Type
withVar x t op = do
  -- push local variable
  ctx <- get
  put (Context  $ M.insert x t (variableMap ctx) )

  -- do the operation
  result <- op

  -- pop local variable out
  put ctx
  return result 


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

eval (EEq e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (ENeq e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (ELt e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (EGt e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (ELe e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool
eval (EGe e1 e2) = comparable e1 >> comparable e2 >> sameType e1 e2 >> return TBool

eval (EIf e1 e2 e3) = isBool e1 >> sameType e2 e3 >> do 
  et <- eval e2
  return et

eval (ELambda (vName,vt) e) = do
  e <- withVar vName vt (eval e)
  return e

eval (EVar vName) = do
  ctx <- get
  case ((variableMap ctx) M.!? vName) of 
    Nothing -> lift $ Left "no such variable"
    Just t -> return t

eval (ELet (vName, e1) e2) = eval e2

eval (ELetRec funcName (vName ,vt) (e1,et1) e2) = eval e2
-- ... more
eval _ = undefined


evalType :: Program -> Either String Type
evalType (Program adts body) = evalStateT (eval body) $
  (Context (M.fromList [])) -- 可以用某种方式定义上下文，用于记录变量绑定状态


simpleEvalExpr expr = evalType (Program [] expr)