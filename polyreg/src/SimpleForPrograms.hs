{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleForPrograms where

import QuantifierFree

import Control.Monad
import Control.Monad.State 
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M


newtype PName = PName String deriving(Eq, Show,Ord)
newtype BName = BName String deriving(Eq, Show,Ord)

-- | Binary operators
-- b = boolean variables
-- p = positions    (ints)
-- l = label values (strings/chars)
data BoolExpr = 
                BConst   Bool
              | BVar     BName
              | BTest    TestOp PName PName
              | BLabelAt PName Char
              | BNot     BoolExpr
              | BBin     BinOp BoolExpr BoolExpr
              deriving(Eq, Show)

data Direction = LeftToRight | RightToLeft deriving(Eq,Show)

-- |  For statement
-- p = position variables
-- b = boolean variables
-- alphabet  = label (alphabet alphabet)
-- output = label (output alphabet)
data ForStmt  = 
             -- assigns to true
               SetTrue BName
             -- if expression
             | If BoolExpr ForStmt ForStmt
             -- for loop with variable a
             -- direction, and using boolean
             -- variables [b].
             | For PName Direction [BName] ForStmt
             -- prints what is a position p
             | PrintPos PName
             -- prints the value "l" directly
             | PrintLbl Char
             -- sequence of statements
             | Seq [ForStmt]
             deriving (Eq, Show)

data ForProgram = ForProgram [BName] [ForStmt] deriving(Eq, Show)


class (Monad m) => MonadInterpreter m where
    throwWithCtx :: String -> m a

    setTrue      :: BName -> m ()
    withBools    :: [BName] -> m a -> m a
    withLoopPos  :: PName -> Direction -> m a -> m [a]

    getPos       :: PName -> m Int
    getBool      :: BName -> m Bool
    getCharAt    :: PName -> m Char


data InterpreterState = InterpreterState {
    input     :: String,
    booleans  :: Map BName Bool,
    posChars  :: Map PName Char,
    positions :: Map PName Int
} deriving (Eq,Show)

data InterpreterError = InterpreterError String InterpreterState  deriving (Eq,Show)

newtype InterM a = InterM (StateT InterpreterState (Except InterpreterError) a)
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError InterpreterError) 

runInterM :: InterM a -> InterpreterState -> Either InterpreterError a 
runInterM (InterM m) s = runExcept $ evalStateT m s

listOldValues :: [BName] -> Map BName Bool -> [(BName, Bool)]
listOldValues [] _ = []
listOldValues (x : xs) m = case M.lookup x m of
    Just b -> (x, b) : listOldValues xs m
    Nothing -> listOldValues xs m

iterWord :: Direction -> String -> [(Int, Char)]
iterWord LeftToRight s = zip [0..] s
iterWord RightToLeft s = reverse (zip [0..] s)

instance MonadInterpreter InterM where
    throwWithCtx msg = do
        s <- get
        throwError $ InterpreterError msg s

    setTrue b = do
        s <- get
        put $ s { booleans = M.insert b True (booleans s) }

    withBools bs m = do
        s <- get
        let oldValues = M.fromList $ listOldValues bs (booleans s)
        put $ s { booleans = (M.fromList $ zip bs (repeat False)) `M.union` (booleans s) }
        r <- m
        modify (\s -> s { booleans = M.union oldValues (booleans s)})
        return r

    withLoopPos p d m = do
        input <- gets input
        forM (iterWord d input) $ \(i, c) -> do
            s <- get
            put $ s { positions = M.insert p i (positions s), posChars = M.insert p c (posChars s)}
            r <- m
            modify (\s -> s { positions = M.delete p (positions s), posChars = M.delete p (posChars s)})
            return r

    getPos p = do
        s <- get
        case M.lookup p (positions s) of
            Just i -> return i
            Nothing -> throwWithCtx $ "Position " ++ show p ++ " not found"

    getBool b = do
        s <- get
        case M.lookup b (booleans s) of
            Just b -> return b
            Nothing -> throwWithCtx $ "Boolean " ++ show b ++ " not found"

    getCharAt p = do
        s <- get
        case M.lookup p (posChars s) of
            Just c -> return c
            Nothing -> throwWithCtx $ "Position " ++ show p ++ " not found"


interpretPosExprM :: (MonadInterpreter m) => PName -> m Int
interpretPosExprM p = getPos p

interpretBoolExprM :: (MonadInterpreter m) => BoolExpr -> m Bool
interpretBoolExprM (BConst b) = return b
interpretBoolExprM (BVar b) = getBool b
interpretBoolExprM (BTest op e1 e2) = (testOpSemantics op) <$> interpretPosExprM e1 <*> interpretPosExprM e2
interpretBoolExprM (BLabelAt p l) = (== l) <$> getCharAt p
interpretBoolExprM (BNot e) = not <$> interpretBoolExprM e
interpretBoolExprM (BBin op e1 e2) = (binOpSemantics op) <$> interpretBoolExprM e1 <*> interpretBoolExprM e2


interpretStmtM :: (MonadInterpreter m) => ForStmt -> m String
interpretStmtM (SetTrue b) = setTrue b >> return ""
interpretStmtM (If e t f) = do
    b <- interpretBoolExprM e
    if b then interpretStmtM t else interpretStmtM f
interpretStmtM (For p d bs stmt) = do
    strings <- withBools bs (withLoopPos p d (interpretStmtM stmt))
    return . concat $ strings
interpretStmtM (PrintPos p) = pure <$> getCharAt p
interpretStmtM (PrintLbl l) = return [l]
interpretStmtM (Seq stmts) = concat <$> mapM interpretStmtM stmts

interpretProgramM :: (MonadInterpreter m) => ForProgram -> m String
interpretProgramM (ForProgram bs stmts) = withBools bs $ (concat <$> mapM interpretStmtM stmts)

interpretProgram :: ForProgram -> InterpreterState -> Either InterpreterError String
interpretProgram p s = runInterM (interpretProgramM p) s


runProgram :: ForProgram -> String -> Either InterpreterError String
runProgram  p s = interpretProgram p (InterpreterState s M.empty M.empty M.empty)
