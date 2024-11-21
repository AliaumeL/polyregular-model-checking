module HighLevelForProgramsInterpreter where

import HighLevelForPrograms

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as M

type Address = Int

type BoolDict = Map Address Bool
type VDict alphabet = Map VarName (VValue alphabet)
type PosDict alphabet = Map VarName (Int, VExpression alphabet)
type AddressDict = Map VarName Address

data InterpreterVals alphabet = InterpreterVals {
    vDict :: VDict alphabet,
    posDict :: PosDict alphabet,
    boolNameToAddr :: AddressDict,
    functions :: Map String (Function alphabet)
}

type InterpreterMonad alphabet = ReaderT (InterpreterVals alphabet) (StateT BoolDict (Either String))


runInterpreter :: InterpreterMonad alphabet x -> InterpreterVals alphabet -> BoolDict -> Either String x
runInterpreter m vals boolDict = evalStateT (runReaderT m vals) boolDict

localWith :: InterpreterVals a -> InterpreterMonad a b -> InterpreterMonad a b
localWith dict m = local (const dict) m

evalBoolExpr :: (Eq alphabet) => BoolExpr alphabet -> InterpreterMonad alphabet Bool
evalBoolExpr (BVar varName) = do
    boolDict <- get
    boolNames <- asks boolNameToAddr
    case M.lookup varName boolNames of
        Just addr -> case M.lookup addr boolDict of
            Just b -> return b
            Nothing -> error $ "Bool variable " ++ varName ++ " mapped to " ++  show addr ++ " not found (values)"
        Nothing -> error $ "Bool variable " ++ varName ++ " not found"
evalBoolExpr (BinOp And b1 b2) = (&&) <$> evalBoolExpr b1 <*> evalBoolExpr b2
evalBoolExpr (BinOp Or b1 b2) = (||) <$> evalBoolExpr b1 <*> evalBoolExpr b2
evalBoolExpr (BinOp Implies b1 b2) = (\x y -> not x || y) <$> evalBoolExpr b1 <*> evalBoolExpr b2
evalBoolExpr (BNot b) = not <$> evalBoolExpr b
evalBoolExpr (BLit b) = return b
evalBoolExpr (BEqVal (VVar varName) (ListLiteral l _)) = do
    vDict <- asks vDict
    case M.lookup varName vDict of
        Just l' -> return $ l == l'
        Nothing -> error $ "Variable " ++ varName ++ " not found "
evalBoolExpr (BEqVal _ _) = error "BEqVal can only compare a variable with a list literal"
evalBoolExpr (BPosBinOp op pos1 pos2) = do
    posDict <- asks posDict
    case (M.lookup pos1 posDict, M.lookup pos2 posDict) of
        (Just (i1, e1), Just (i2, e2)) -> do 
            if e1 /= e2 then error $ "Compared position variables " ++ pos1 ++ " and " ++ pos2 ++ "come from different lists" else return ()
            case op of
                PosEq -> return $ i1 == i2
                PosNeq -> return $ i1 /= i2
                PosLeq -> return $ i1 <= i2
                PosGeq -> return $ i1 >= i2
                PosLt -> return $ i1 < i2
                PosGt -> return $ i1 > i2
        _ -> error $ "Position variables " ++ pos1 ++ " and " ++ pos2 ++ " not found"

evalVExpression :: (Eq alphabet) => VExpression alphabet -> InterpreterMonad alphabet (VValue alphabet)
evalVExpression (ListLiteral l _) = return l 
evalVExpression (ListConstructor exprs) = do
    exprs' <- mapM evalVExpression exprs
    return $ VList exprs'
evalVExpression (ListExpression block) = do
    env <- ask 
    let envWithClearedBools = env {boolNameToAddr = M.empty}
    VList <$> (localWith envWithClearedBools $ evalBlock block)
evalVExpression (VVar varName) = do
    vDict <- asks vDict
    case M.lookup varName vDict of
        Just v -> return v
        Nothing -> error $ "List variable " ++ varName ++ " not found "
evalVExpression (VRev e) = do
    e' <- evalVExpression e
    case e' of
        VList l -> return $ VList $ reverse l
        _ -> error "VRev can only reverse a list"
evalVExpression (VFunctionCall f args) = do
    functions <- asks functions
    case M.lookup f functions of
        Nothing -> error $ "Function " ++ f ++ " not found"
        Just f -> evalFunction f args

evalStatement :: (Eq alphabet) => Statement alphabet -> InterpreterMonad alphabet [(VValue alphabet)]
evalStatement (For posVar valVar listExpr block) = do 
    list <- evalVExpression listExpr
    case list of
        VChar _ -> error "For loop can only iterate over a list"
        VList list -> do
            let enumList = zip [0..] list
            ans <- forM enumList $ \(i, v) -> do
                vDict <- asks vDict
                posDict <- asks posDict
                let posDict' = M.insert posVar (i, listExpr) posDict
                let vDict' = M.insert valVar v vDict
                env <- ask 
                let newEnv = env {vDict = vDict', posDict = posDict'}
                localWith newEnv $ evalBlock block
            return $ concat ans
evalStatement (If b s1 s2) = do
    b' <- evalBoolExpr b
    concat <$> (mapM evalStatement $ if b' then s1 else s2)
evalStatement (Yield e) = do
    x <- evalVExpression e
    return [x]
evalStatement (Let varName e stmt) = do
    v <- evalVExpression e
    vDict <- asks vDict
    if M.member varName vDict then error $ "Variable " ++ varName ++ " already defined -- for now, we do not allow shadowing" else return ()
    let vDict' = M.insert varName v vDict
    env <- ask 
    let newEnv = env {vDict = vDict'}
    localWith newEnv $ evalStatement stmt
evalStatement (SetTrue varName) = do
    boolDict <- get
    boolNames <- asks boolNameToAddr
    case M.lookup varName boolNames of
        Just addr -> put $ M.insert addr True boolDict
        Nothing -> error $ "Bool variable " ++ varName ++ " not found"
    return []

allocBool :: InterpreterMonad alphabet Address
allocBool = do
    boolDict <- get
    let maxUsedM = fst <$> M.lookupMax boolDict 
    let maxUsed = maybe 0 id maxUsedM
    let addr = maxUsed + 1
    put $ M.insert addr False boolDict
    return addr

evalBlock :: (Eq alphabet) => StatementBlock alphabet -> InterpreterMonad alphabet [(VValue alphabet)]
evalBlock (StatementBlock vars stmts _ ) = do 
    addrs <- mapM (\_ -> allocBool) vars
    boolNames <- asks boolNameToAddr
    let boolNames' = foldr (\(varName, addr) dict -> M.insert varName addr dict) boolNames (zip vars addrs) 
    oldEnv <- ask
    let newEnv = oldEnv {boolNameToAddr = boolNames'}
    ans <- concat <$> (localWith newEnv $ mapM evalStatement stmts)
    modify $ \d -> Prelude.foldr (\addr dict -> M.delete addr dict) d addrs 
    return ans

processArg :: (Eq alphabet) => (VarName, ArgType alphabet) -> Expression alphabet -> (VDict alphabet, PosDict alphabet) -> InterpreterMonad alphabet (VDict alphabet, PosDict alphabet)
processArg (varName, TVal _) (ValExpr e) (vDict, posDict) = do
    v <- evalVExpression e
    return (M.insert varName v vDict, posDict)
processArg (varName, TVal _) _ _ = error $ "Expected a letter/list for variable " ++ varName
processArg (varName, TPos _) (PosExpr posVar) (vDict, createdPosDict) = do
    posDict <- asks posDict
    case M.lookup posVar posDict of
        Just (i, e') -> do
            return (vDict, M.insert varName (i, e') createdPosDict)
        Nothing -> error $ "Position variable " ++ posVar ++ " not found" 
processArg (varName, TPos _) _ _ = error $ "Expected a position for variable " ++ varName

evalFunction :: (Eq alphabet) => Function alphabet -> [Expression alphabet] -> InterpreterMonad alphabet (VValue alphabet)
evalFunction (Function _ args block) vals = do
    if length vals /= length args then error "Incorrect number of arguments" else return ()
    (vDict', posDict') <- foldM (\dicts (arg, expr) -> processArg arg expr dicts) (M.empty, M.empty) (zip args vals) 
    env <- ask 
    let newEnv = env {vDict = vDict', posDict = posDict', boolNameToAddr = M.empty}
    VList <$> (localWith newEnv $ evalBlock block)

evalFunctions :: (Eq alphabet) => [Function alphabet] -> [alphabet] -> InterpreterMonad alphabet (VValue alphabet)
evalFunctions fs input = do
    let fs' = M.fromList $ map (\f -> (name f, f)) fs
    let env = InterpreterVals M.empty M.empty M.empty fs'
    let input' = VList $  map (VChar) input
    case M.lookup "main" fs' of
        Just main -> localWith env $ evalFunction main [ValExpr $ ListLiteral input' (TList TChar)]
        Nothing -> error "No main function found"

runForProgram :: (Eq alphabet) => [Function alphabet] -> [alphabet] -> Either String (VValue alphabet)
runForProgram fs input = runInterpreter (evalFunctions fs input) (InterpreterVals M.empty M.empty M.empty (M.fromList $ map (\f -> (name f, f)) fs)) M.empty
