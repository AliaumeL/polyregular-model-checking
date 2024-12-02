module ForProgramsTyping where

import ForPrograms

import Data.Map    (Map)
import qualified Data.Map as Map
import Control.Monad

data OutputType = TUnit
                | TOList OutputType
                | TOChar
                deriving (Show, Eq)

data Position = Position (OExpr String ()) OutputType
    deriving (Show, Eq)

data Argument = Argument OutputType Int 
    deriving (Show, Eq)

data FunctionType = FProd [Argument] OutputType
                  | FPred [Argument]
    deriving (Show, Eq)


data ValueType = TBool | TPos Position | TOutput OutputType | TConst OutputType
    deriving (Show, Eq)


data TypingContext = TypingContext {
    funcs :: Map String FunctionType,
    vars  :: Map String ValueType
}

getFuncPred :: TypingContext -> String -> Maybe [Argument]
getFuncPred ctx v = do
    FPred args <- Map.lookup v (funcs ctx)
    return args

getFuncProd :: TypingContext -> String -> Maybe ([Argument], OutputType)
getFuncProd ctx v = do 
    FProd args t <- Map.lookup v (funcs ctx)
    return (args, t)

getConst :: TypingContext -> String -> Maybe OutputType
getConst ctx v = do 
    TConst t <- Map.lookup v (vars ctx)
    return t

getPos :: TypingContext -> String -> Maybe Position
getPos ctx v = do
    TPos p <- Map.lookup v (vars ctx)
    return p

getOutput :: TypingContext -> String -> Maybe OutputType
getOutput ctx v = do
    TOutput t <- Map.lookup v (vars ctx)
    return t

getBool :: TypingContext -> String -> Maybe ()
getBool ctx v = do
    TBool <- Map.lookup v (vars ctx)
    return ()

{-

typeCheckBoolExpr :: TypingContext -> BExpr String ValueType -> Maybe ()
typeCheckBoolExpr ctx (BConst _ TBool) = Just ()
typeCheckBoolExpr ctx (BNot e TBool) = typeCheckBoolExpr ctx e
typeCheckBoolExpr ctx (BOp _ e1 e2 TBool) = do
    t1 <- typeCheckBoolExpr ctx e1
    t2 <- typeCheckBoolExpr ctx e2
    return ()
typeCheckBoolExpr ctx (BComp _ e1 e2 TBool) = do
    (Position o1) <- typeCheckPosExpr ctx e1
    (Position o2) <- typeCheckPosExpr ctx e2
    guard (o1 == o2)
    return ()
typeCheckBoolExpr ctx (BVar v TBool) = getBool ctx v
typeCheckBoolExpr ctx (BGen s TBool) = typeCheckStmt ctx s
typeCheckBoolExpr ctx (BApp v args TBool) = do
    args' <- getFuncPred ctx v
    targs <- mapM (typeCheckArg ctx) args
    guard (args' == targs)
    return ()
typeCheckBoolExpr ctx (BLitEq c o TBool) = do
    t1 <- typeCheckConstExpr  ctx c
    t2 <- typeCheckOutputExpr ctx o
    guard (t1 == t2)
    return ()
typeCheckBoolExpr ctx _ = Nothing

typeCheckPosExpr :: TypingContext -> PExpr String ValueType -> Maybe Position
typeCheckPosExpr ctx (PVar v t) = getPos ctx v 

typeCheckConstExpr :: TypingContext -> CExpr String ValueType -> Maybe OutputType
typeCheckConstExpr ctx (CChar _ (ConstExpr TOChar)) = Just TOChar
typeCheckConstExpr ctx (CUnit (ConstExpr TUnit)) = Just TUnit
typeCheckConstExpr ctx (CList xs (ConstExpr (TOList t))) = do
    ts <- mapM (typeCheckConstExpr ctx) xs
    if all (== t) ts then Just (TOList t) else Nothing

typeCheckOutputExpr :: TypingContext -> OExpr String ValueType -> Maybe OutputType
typeCheckOutputExpr ctx (OVar v (DynExpr t)) = do
    t' <- getOutput ctx v
    guard (t == t')
    return t
typeCheckOutputExpr ctx (OConst c (DynExpr t)) = do
    (ConstExpr t') <- typeCheckConstExpr ctx c
    guard (t == t')
    return t
typeCheckOutputExpr ctx (OList xs (DynExpr (TOList t))) = do
    ts <- mapM (typeCheckOutputExpr ctx) xs
    if all (== t) ts then Just (DynExpr (TOList t)) else Nothing
typeCheckOutputExpr ctx (ORev o (DynExpr t)) = do
    t' <- typeCheckOutputExpr ctx o
    guard (t == t')
    return t
typeCheckOutputExpr ctx (OIndex o p (DynExpr t)) = do
    t' <- typeCheckOutputExpr ctx o
    (Position t'') <- typeCheckPosExpr ctx p
    guard (o == t'')
    return t
typeCheckOutputExpr ctx (OApp v args (DynExpr t)) = do
    (args', t') <- getFuncProd ctx v
    targs <- mapM (typeCheckArg ctx) args
    guard (args' == targs)
    return t
typeCheckOutputExpr ctx (OGen s (DynExpr t)) = typeCheckStmt ctx s


typeCheckStmt :: TypingContext -> Stmt String ValueType -> Maybe ValueType
typeCheckStmt ctx (SIf e s1 s2 t) = do
    typeCheckBoolExpr ctx e
    t1 <- typeCheckStmt ctx s1
    t2 <- typeCheckStmt ctx s2
    guard (t1 == t2)
    guard (t == t1)
    return t
typeCheckStmt ctx (SYield o (DynExpr (OList t))) = do
    t' <- typeCheckOutputExpr ctx o
    guard (t == t')
    return (DynExpr (OList t))
typeCheckStmt ctx (SOReturn o t) = typeCheckOutputExpr ctx o
typeCheckStmt ctx (SBReturn b t) = typeCheckBoolExpr ctx b
typeCheckStmt ctx (SLetOutput v o s t) = do
    t' <- typeCheckOutputExpr ctx o
    let ctx' = ctx {vars = Map.insert v t' (vars ctx)}
    typeCheckStmt ctx' s
typeCheckStmt ctx (SLetBoolean v s t) = do
    let ctx' = ctx {vars = Map.insert v TBool (vars ctx)}
    typeCheckStmt ctx' s
typeCheckStmt ctx (SSetTrue v t) = just t
typeCheckStmt ctx (SFor (v1, v2) o s t) = do
    (Position o') <- typeCheckPosExpr ctx o
    let ctx' = ctx {vars = Map.insert v1 (Position o') (vvars ctx)}
    typeCheckStmt ctx' s
typeCheckStmt ctx (SSeq ss t) = do
    ts <- mapM (typeCheckStmt ctx) ss
    guard (all (== t) ts)
    return t

typeCheckArg :: TypingContext -> OExpr String ValueType -> [PExpr String ValueType] -> Maybe Argument
typeCheckArg ctx o ps = do
    t <- typeCheckOutputExpr ctx o
    ts <- mapM (typeCheckPosExpr ctx) ps
    return (Argument t ts)

typeCheckFunction :: TypingContext -> StmtFun String ValueType -> Maybe ()
typeCheckFunction ctx (StmtFun v args s t) = do
    let ctx' = ctx {funcs = Map.insert v (FProd args (DynExpr t)) (funcs ctx)}
    typeCheckStmt ctx' s

typeCheckProgram :: [StmtFun String ValueType] -> Maybe ()
typeCheckProgram fs = do
    let ctx = TypingContext Map.empty Map.empty Map.empty Map.empty
    mapM (typeCheckFunction ctx) fs
-}
