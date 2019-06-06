-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalType :: Program -> Maybe Type 就行。
module EvalType where

import AST
import Control.Monad.State
import qualified Data.Map.Strict as M

data Context = Context { variableMap :: M.Map String Type,
                          eDataTypeMap :: M.Map String Type,  -- 构造函数和adt 类型的映射
                          constructors :: M.Map String [Type],  -- 构造函数和需要的类型数组
                          constructorTypeMap :: M.Map String Type 
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
  put (Context  (M.insert x t (variableMap ctx))  (eDataTypeMap ctx) (constructors ctx) (constructorTypeMap ctx))

  -- do the operation
  result <- op

  -- pop local variable out
  put ctx
  return result 

withVars :: [(String,Type)] -> ContextState Type -> ContextState Type
withVars ((vName,vt):vs) op = withVar vName vt (withVars vs op)
withVars [] op = op

-- operation with local function 
withFunc :: String -> Type -> Type -> ContextState Type -> ContextState Type
withFunc x t1 t2 op = do
  ctx <- get
  put (Context (M.insert x (TArrow t1 t2) (variableMap ctx))   (eDataTypeMap ctx) (constructors ctx) (constructorTypeMap ctx))

  result <- op

  put ctx
  return result

checkFuncRetType :: String -> String -> Type -> Expr -> Type -> ContextState Type
checkFuncRetType funcName vName vt expr rt = do
  ctx <- get
  put $ (Context (M.insert funcName (TArrow vt rt) (variableMap ctx))   (eDataTypeMap ctx) (constructors ctx) (constructorTypeMap ctx))
  et <- withVar vName vt (eval expr)
  put ctx
  case et == rt of
    True -> return $ TArrow vt rt
    False -> lift  Nothing

checkFuncApply :: Type -> Type ->ContextState Type
checkFuncApply vt (TArrow t1 t2) = case vt == t1 of
  True -> return t2
  False -> lift  Nothing

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
    Nothing -> case ((constructorTypeMap ctx) M.!? vName) of
      Nothing -> lift Nothing
      Just t -> return t
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
  checkPatternsType (fst $ unzip ps) (replicate (length ps) et)
  rt <- checkPatternExprTypes ps et
  return rt

eval (EData cons exprs) = do
  ctx <- get
  case ((eDataTypeMap ctx) M.!? cons) of
    Just ct ->
      case ((constructors ctx) M.!? cons) of
        Just ts -> case ((length exprs) == (length ts)) of
          True -> do 
            checkEDataTypes exprs ts
            return $ ct
          False -> lift Nothing 
        Nothing -> lift Nothing
    Nothing -> lift Nothing

-- eval _ = undefined

evalType :: Program -> Maybe Type
evalType (Program adts body) = evalStateT (eval body) $ (Context (M.fromList $ []) (M.fromList $ constructorTypesFromADTs adts) (M.fromList $ constructorContentFromADTs adts) (M.fromList $ getADTsConsFuncsType adts)) -- 可以用某种方式定义上下文，用于记录变量绑定状态

-- 生成 构造函数的类型 dt：最终类型
conApply dt [] = dt
conApply dt (t:ts) = TArrow t (conApply dt ts)

-- 生成 一列构造函数的类型
conApplys dt ((name,ts):cons) = (name ,(conApply dt ts)) : (conApplys dt cons)
conApplys dt [] = []

-- 生成adt的所有构造函数的类型
adtApplys (ADT name cons) = conApplys (TData name) cons

-- 生成一列adt的所有构造函数的类型
adtsApplys [] = []
adtsApplys (adt:adts) = (adtApplys adt) ++ (adtsApplys adts)


-- 生成 adt 相关的全局环境
constructorTypesFromADT (ADT name ax) = foldl (\acc x-> (x,TData name) : acc) [] (fst $ unzip ax)
constructorTypesFromADTs adts = foldl (\acc x -> (constructorTypesFromADT x) ++ acc) [] adts

constructorContentFromADT (ADT name ax) = ax
constructorContentFromADTs adts = foldl (\acc x -> (constructorContentFromADT x) ++ acc) [] adts

point = (ADT "Point" [("point",[TInt,TInt])])
line = (ADT "line" [("points",[TData "Point",TData "Point"]),("kb",[TInt ,TInt ])])
person = ADT "Person" [("man",[TInt,TBool]),("woman",[TChar,TBool])]
adts = [line,person,point]
simpleEvalExpr expr = evalType (Program adts expr)


-- 检查代数数据类型的模式和构造函数类型一样
checkPDataType :: Pattern -> ContextState Type
checkPDataType (PData s ps) = do
  ctx <- get
  case ((constructors ctx) M.!? s) of
    Nothing -> lift Nothing
    Just ts -> checkPatternsType ps ts >> case ((eDataTypeMap ctx) M.!? s) of
      Just t -> return t
      Nothing -> lift Nothing

-- 检查一列模式的类型
checkPatternsType :: [Pattern] -> [Type] -> ContextState Type
checkPatternsType (p:ps) (t:ts) = do 
  pType <- (checkPatternType p t)
  psType <- (checkPatternsType ps ts)
  return psType
checkPatternsType [] [] = do
  return TBool

-- 检查单个模式的
checkPatternType :: Pattern -> Type -> ContextState Type
checkPatternType p t = do
  case p of
    PBoolLit b -> 
      case (t == TBool) of
        True -> return TBool
        _ -> lift Nothing
    PIntLit i -> 
      case (t == TInt) of
        True -> return TInt
        _ -> lift Nothing
    PCharLit c -> 
      case (t == TChar) of
        True -> return TChar
        _ -> lift Nothing
    PVar s -> return t
    PData cons ps -> do
      ctx <- get
      case ((eDataTypeMap ctx) M.!? cons) of
        Nothing -> lift Nothing
        Just dt -> case dt == t of
          True -> checkPDataType (PData cons ps)
          False -> lift Nothing


getVarInPData :: Pattern -> Type -> ContextState [(String,Type)]
getVarInPData (PData cons ps) t = do
  ctx <- get
  case ((constructors ctx) M.!? cons) of
    Just ts -> getVarInPatterns ps ts

getVarInPatterns :: [Pattern] -> [Type] -> ContextState [(String,Type)]
getVarInPatterns (p:ps) (t:ts) = do
  varP <- getVarInPattern p t
  varPs <- getVarInPatterns ps ts
  return (varP ++ varPs)
getVarInPatterns [] [] = do
  return []

getVarInPattern :: Pattern -> Type -> ContextState [(String,Type)]
getVarInPattern p t = do
  case p of
    PVar vName -> return [(vName,t)] 
    PData cons ps -> getVarInPData p t
    _ -> return []

getPatternExprType :: Pattern -> Type -> Expr -> ContextState Type
getPatternExprType p pt expr = do
  vars <- getVarInPattern p pt
  withVars vars (eval expr)

checkPatternExprTypes :: [(Pattern,Expr)] -> Type -> ContextState Type
checkPatternExprTypes ((p,expr):[]) pt = do
  t <- getPatternExprType p pt expr
  return t
checkPatternExprTypes ((p,expr):pes) pt = do
  t1 <- getPatternExprType p pt expr
  t2 <- checkPatternExprTypes pes pt
  case t1 == t2 of
    False -> lift Nothing
    True -> return t1


checkDataType :: Expr -> Type -> ContextState Type
checkDataType e t = do
  et <- eval e
  case et == t of
    True -> return et
    False -> lift Nothing

checkEDataTypes :: [Expr] -> [Type] -> ContextState [Type]
checkEDataTypes (e:es) (t:ts) = do
  et <- checkDataType e t
  est <- checkEDataTypes es ts
  return (et: est)
checkEDataTypes [] [] = do
  return []

getADTsConsFuncsType (adt:adts) = (getAdtConsFuncsType adt) ++ (getADTsConsFuncsType adts)
getADTsConsFuncsType [] = [] 

getAdtConsFuncsType (ADT tname cs) = getConsFuncsType tname cs;
getConsFuncsType tname ((name,ts):cs) = (name,(getConsFuncType tname (ts))):(getConsFuncsType tname cs)
getConsFuncsType tname [] = []
getConsFuncType tname (t:ts) = TArrow t (getConsFuncType tname ts)
getConsFuncType tname [] = TData tname
