{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForProgramInterpreter where

import Control.Monad
import Control.Monad.State 
import Control.Monad.Except
import qualified Data.Map as M
import Data.Tuple.Extra

import QuantifierFree
import ForPrograms 

data Value = VBool Bool | VOutput (CExpr String ()) deriving (Show, Eq)
data StmtValue = StmtNoOp | StmtReturn Value | StmtYield Value deriving (Show, Eq)

instance Semigroup Value where
    VOutput x <> VOutput y = VOutput (x <> y)
    x <> y = error  $ "Cannot concatenate " ++ show x ++ " and " ++ show y

instance Semigroup StmtValue where
    StmtNoOp <> x = x
    x <> StmtNoOp = x
    (StmtReturn x) <> _ = StmtReturn x
    (StmtYield x) <> (StmtYield y) = StmtYield (x <> y)
    (StmtYield x) <> (StmtReturn y) = StmtReturn (x <> y)

instance Monoid StmtValue where
    mempty = StmtNoOp


data InterpreterState = InterpreterState {
    vDict :: M.Map String (CExpr String ()),
    posDict :: M.Map String Int,
    bools :: M.Map String Bool ,
    functions :: M.Map String (StmtFun String ()) 
} deriving (Show, Eq)

data InterpretError = InterpretError String InterpreterState deriving (Show, Eq)

class (Monad m) => MonadInterpreter m where
    withValue   :: String -> CExpr String () -> m a -> m a
    withValues  :: [(String, CExpr String ())] -> m a -> m a
    withPos     :: String -> Int -> m a -> m a
    withPositions :: [(String, Int)] -> m a -> m a
    withBoolean :: String -> m a -> m a
    withFunctions :: [StmtFun String ()] -> m a -> m a 
    setTrueBoolean  :: String -> m ()
    withCleanEnvironment :: m a -> m a

    getPos      :: String -> m Int
    getValue    :: String -> m (CExpr String ())
    getBoolean  :: String -> m Bool
    getFunction :: String -> m (StmtFun String ())

    throwWithCtx :: String -> m a


newtype InterpreterMonad a = InterpretMonad (StateT InterpreterState (Except InterpretError) a)
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError InterpretError)



instance MonadInterpreter InterpreterMonad where
    withCleanEnvironment m = do
        currentState <- get
        put (emptyInterpreterState {functions = functions currentState})
        v <- m
        put currentState
        return v
    withPos name pos m = do
        currentState <- get
        let newState = currentState {posDict = M.insert name pos (posDict currentState)}
        put newState
        v <- m
        modify $ restoreAllExceptBooleans currentState
        return v
    withPositions vals m = do
        currentState <- get
        let newState = currentState {posDict = M.union (posDict currentState) (M.fromList vals)}
        put newState
        v <- m
        modify $ restoreAllExceptBooleans currentState
        return v
    withValue name val m = do
        currentState <- get
        let newState = currentState {vDict = M.insert name val (vDict currentState)}
        put newState
        v <- m
        modify $ restoreAllExceptBooleans currentState
        return v
    withValues vals m = do
        currentState <- get
        let newState = currentState {vDict = M.union (vDict currentState) (M.fromList vals)}
        put newState
        v <- m
        modify $ restoreAllExceptBooleans currentState
        return v
    withBoolean name m = do
        currentState <- get
        let newState = currentState {bools = M.insert name False (bools currentState)}
        put newState
        v <- m
        modify $ (\currentState -> currentState {bools = M.delete name (bools currentState)})
        return v
    withFunctions funcs m = do
        currentState <- get
        let newState = currentState {functions = M.union (functions currentState) (M.fromList $ map (\f -> (funName f, f)) funcs)}
        put newState
        v <- m
        modify $ restoreAllExceptBooleans currentState
        return v
    setTrueBoolean name = do 
        currentState <- get
        case M.lookup name (bools currentState) of
            Nothing -> throwWithCtx $ "Boolean " ++ name ++ " not found"
            Just _ -> modify $ \currentState -> currentState {bools = M.insert name True (bools currentState)}
    getValue name = do
        currentState <- get
        case M.lookup name (vDict currentState) of
            Just val -> return val
            Nothing -> throwWithCtx $ "Value " ++ name ++ " not found"
    getBoolean name = do
        currentState <- get
        case M.lookup name (bools currentState) of
            Just val -> return val
            Nothing -> throwWithCtx $ "Boolean " ++ name ++ " not found"
    getFunction name = do
        currentState <- get
        case M.lookup name (functions currentState) of
            Just f -> return f
            Nothing -> throwWithCtx $ "Function " ++ name ++ " not found"
    getPos name = do
        currentState <- get
        case M.lookup name (posDict currentState) of
            Just pos -> return pos
            Nothing -> throwWithCtx $ "Position " ++ name ++ " not found"
    throwWithCtx msg = do
        currentState <- get
        throwError $ InterpretError msg currentState


emptyInterpreterState :: InterpreterState
emptyInterpreterState = InterpreterState {
    vDict = M.empty,
    posDict = M.empty,
    bools = M.empty,
    functions = M.empty
}

runInterpreterMonad :: InterpreterMonad a -> Either InterpretError a
runInterpreterMonad (InterpretMonad m) = runExcept (evalStateT m emptyInterpreterState)


runProgram :: Program String () -> CExpr String () -> Either InterpretError (CExpr String ())
runProgram p i = runInterpreterMonad $ interpretProgram p i

runProgramString :: Program String () -> String -> Either InterpretError String
runProgramString p i = runInterpreterMonad $ runProgramStringM p i


runProgramStringM :: (MonadInterpreter m) => Program String () -> String -> m String
runProgramStringM p i = do
    o <- interpretProgram p (CList (map (\c -> CChar c ()) i) ())
    case o of
        CList l _ -> forM l $ \x -> case x of
            CChar c _ -> return c
            CList _ _ -> throwWithCtx $ "Expected list of characters as output of function" ++ show o
        _ -> throwWithCtx $ "Expected list of characters as input of function" ++ show o

restoreAllExceptBooleans :: InterpreterState -> InterpreterState -> InterpreterState
restoreAllExceptBooleans old new = old { bools = bools new }


interpretProgram :: (MonadInterpreter m) => Program String () -> CExpr String () -> m (CExpr String ())
interpretProgram (Program funcs v) input = withFunctions funcs $
    interpretOExpr (OApp v [(OConst input (), [])] ())

interpretFunction :: (MonadInterpreter m) => StmtFun String () -> [(CExpr String (), [Int])] -> m Value 
interpretFunction (StmtFun _ args stmt _) args' = do
    let argsO = zip (map fst3 args) (map fst args')
    let argsP = zip (concatMap thd3 args) (concatMap snd args')
    withCleanEnvironment $ withValues argsO $ withPositions argsP $ do
        outputValue <- interpretStmt stmt
        case outputValue of
            StmtReturn v -> return v
            StmtYield v  -> return v
            StmtNoOp     -> return (VOutput (CList [] ()))

interpretStmt :: (MonadInterpreter m) => Stmt String () -> m StmtValue
interpretStmt (SSetTrue b _) = setTrueBoolean b >> return StmtNoOp
interpretStmt (SLetBoolean b stmt _) = withBoolean b $ interpretStmt stmt
interpretStmt (SLetOutput (v, _) e stmt _) = do
    e' <- interpretOExpr e
    withValue v e' $ interpretStmt stmt
interpretStmt (SIf b stmt1 stmt2 _) = do
    b' <- interpretBExpr b
    if b' then interpretStmt stmt1 else interpretStmt stmt2
interpretStmt (SYield e _) = StmtYield . VOutput . (flip CList ()) . pure <$> interpretOExpr e
interpretStmt (SOReturn e _) = StmtReturn . VOutput <$> interpretOExpr e
interpretStmt (SBReturn b _) = StmtReturn . VBool <$> interpretBExpr b
interpretStmt (SSeq stmts _) = mconcat <$> mapM interpretStmt stmts
interpretStmt (SFor (i, v, _) (ORev e _) stmt _) = do
    e' <- interpretOExpr e
    case e' of
        CChar c _ -> throwWithCtx $ "Cannot iterate over character " ++ show e ++ " which is " ++ show c
        CList l _ -> do
            let l' = reverse $ zip [0..] l
            mconcat <$> (forM l' $ \(index, currentValue) -> do
                withValue v currentValue $ withPos i index $ interpretStmt stmt)
interpretStmt (SFor (i, v, _) e stmt _) = do
    e' <- interpretOExpr e
    case e' of
        CChar c _ -> throwWithCtx $ "Cannot iterate over character " ++ show e ++ " which is " ++ show c
        CList l _ -> do
            let l' = zip [0..] l
            mconcat <$> (forM l' $ \(index, currentValue) -> do
                withValue v currentValue $ withPos i index $ interpretStmt stmt)

interpretBExpr :: (MonadInterpreter m) => BExpr String () -> m Bool
interpretBExpr (BConst b _) = return b
interpretBExpr (BNot b _) = not <$> interpretBExpr b
interpretBExpr (BOp Conj b1 b2 _) = (&&) <$> interpretBExpr b1 <*> interpretBExpr b2
interpretBExpr (BOp Disj b1 b2 _) = (||) <$> interpretBExpr b1 <*> interpretBExpr b2
interpretBExpr (BComp Eq p1 p2 _) = (==) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BComp Neq p1 p2 _) = (/=) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BComp Lt p1 p2 _) = (<) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BComp Gt p1 p2 _) = (>) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BComp Le p1 p2 _) = (<=) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BComp Ge p1 p2 _) = (>=) <$> interpretPExpr p1 <*> interpretPExpr p2
interpretBExpr (BVar v _) = getBoolean v
interpretBExpr (BGen stmt _) = do 
    v <- interpretStmt stmt
    case v of
        StmtReturn (VBool b) -> return b
        _ -> throwWithCtx $ "Expected boolean return value, got " ++ show v
interpretBExpr (BApp v args _) = do
    f <- getFunction v
    evaluatedArgs <- interpretArgs args
    o <- interpretFunction f evaluatedArgs
    case o of
        VBool b -> return b
        _ -> throwWithCtx $ "Expected boolean return value, got " ++ show o
interpretBExpr (BLitEq _ c o _) = do
    c' <- interpretCExpr c
    o' <- interpretOExpr o
    return $ c' == o'

interpretArgs :: (MonadInterpreter m) => [(OExpr String (), [PExpr String ()])] -> m [(CExpr String (), [Int])]
interpretArgs = mapM $ \(o, ps) -> do
    o' <- interpretOExpr o
    ps' <- mapM interpretPExpr ps
    return (o', ps')

interpretPExpr :: (MonadInterpreter m) => PExpr String () -> m Int
interpretPExpr (PVar v _) = getPos v
    
defaultOValue :: OutputType -> CExpr String ()
defaultOValue TOChar = CChar '🎁' ()
defaultOValue (TOList t) = CList [] ()


interpretOExpr :: (MonadInterpreter m) => OExpr String () -> m (CExpr String ())
interpretOExpr (OVar v _) = getValue v
interpretOExpr (OConst c _) = return c
interpretOExpr (OList l _) = CList <$> mapM interpretOExpr l <*> pure ()
interpretOExpr (ORev o _) = do
    o' <- interpretOExpr o
    case o' of
        CList l _ -> return $ CList (reverse l) ()
        _ -> throwWithCtx $ "(Rev) Expected list, got " ++ show o'
interpretOExpr (OIndex o p _) = do
    o' <- interpretOExpr o
    p' <- interpretPExpr p
    case o' of
        CList l _ -> return $ l !! p'
        _ -> throwWithCtx $ "(Index) Expected list, got " ++ show o'
interpretOExpr (OApp v args _) = do
    f <- getFunction v
    evaluatedArgs <- interpretArgs args
    o <- interpretFunction f evaluatedArgs
    case o of
        VOutput x -> return x
        _ -> throwWithCtx $ "(OApp) Expected output value, got " ++ show o
interpretOExpr (OGen stmt _) = do
    v <- interpretStmt stmt
    case v of
        StmtReturn (VOutput o) -> return o
        StmtYield (VOutput o) -> return o
        _ -> throwWithCtx $ "(OGen) Expected output value, got " ++ show v

interpretCExpr :: (MonadInterpreter m) => CExpr String () -> m (CExpr String ())
interpretCExpr (CChar c _) = return $ CChar c ()
interpretCExpr (CList l _) = CList <$> mapM interpretCExpr l <*> pure ()



