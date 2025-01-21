{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.HighLevel.ToSimple where

-- This converts a ForProgram to a SimpleForProgram
-- assuming 
--
-- 1) The ForProgram does not contain
--    a. any let bindings for oexpressions
--    b. any iterator over a non-variable
--    c. variables of type other than Bool, Char, [Char] and Pos
--    d. any function calls
--    e. any literal values other than the empty list and characters
--    f. any literal equality test other than of the form "var = char"
--    g. any "return" statment
--    e. any generator expression
-- 2) The ForProgram cannot use Let bindings for booleans outside of
--    a. a let binding for a boolean 
--    b. as an immediate child of a for-loop
--    c. as a first statement of a function
-- 3) The ForProgram must contain a function corresponding to the "main"
--    entrypoint that has type [Char] -> [Char]
--    and takes no position variables as input

import ForPrograms.HighLevel        as FP
import ForPrograms.Simple           as SFP

import ForPrograms.HighLevel.Transformations.FinalConditions (finalConditions, displayBrokenConditions)

import Debug.Trace (traceM)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M

data ToSimpleForProgramError = 
    LetBindingOExpression
  | IteratorOverNonVariable
  | YieldNonCharOrVar
  | NonBoolVariable
  | FunctionCall
  | LiteralValue
  | LiteralEqualityTest
  | ReturnStatement
  | LetBindingBoolean
  | GeneratorExpression
  | NoMainFunction
  | DisplayBrokenConditions String
  deriving (Show,Eq)

class (Monad m) => MonadTSF m where
    guardOrThrow :: ToSimpleForProgramError -> Bool -> m ()
    withPosition :: String -> String -> m a -> m a
    getPosition  :: String -> m SFP.PName

newtype TSFPMonad a = TSFPMonad (ReaderT (Map String PName) (Except ToSimpleForProgramError) a) 
    deriving (Functor, Applicative, Monad, MonadReader (Map String PName), MonadError ToSimpleForProgramError)

instance MonadTSF TSFPMonad where
    guardOrThrow e b = unless b $ throwError e
    withPosition i e m = local (M.insert e (SFP.PName i)) m
    getPosition i = do
        pos <- asks (M.lookup i)
        case pos of
            Just p -> return p
            Nothing -> throwError $ IteratorOverNonVariable

runTSFPMonad :: TSFPMonad a -> Either ToSimpleForProgramError a
runTSFPMonad (TSFPMonad m) = runExcept $ runReaderT m M.empty


findMainFunction :: [StmtFun String t] -> String -> TSFPMonad (FP.StmtFun String t)
findMainFunction [] main = throwError NoMainFunction
findMainFunction (StmtFun name args body outputType :fs) main = 
    if name == main then return $ StmtFun name args body outputType
    else findMainFunction fs main


toSimpleForProgram :: (Show t) => FP.Program String t -> Either ToSimpleForProgramError SFP.ForProgram
toSimpleForProgram p = do 
    if finalConditions p then 
        runTSFPMonad (toSimpleForProgramM p)
    else 
        Left $ DisplayBrokenConditions $ displayBrokenConditions p


toSimpleForProgramM :: (Show t) => FP.Program String t -> TSFPMonad SFP.ForProgram
toSimpleForProgramM (FP.Program funcs main) = do
    FP.StmtFun _ args body outputType <- findMainFunction funcs main
    (bools, stmt) <- forLoopBodyToSimpleForProgram body
    return $ SFP.ForProgram bools stmt


collectBooleans :: FP.Stmt String t -> TSFPMonad ([SFP.BName], FP.Stmt String t)
collectBooleans (FP.SLetBoolean v e _) = do
    (bools, stmt) <- collectBooleans e
    return (BName v : bools, stmt)
collectBooleans stmt = return ([], stmt)

-- This function extracts all the "let booleans" and extracts them
forLoopBodyToSimpleForProgram :: (Show t) => FP.Stmt String t -> TSFPMonad ([SFP.BName], SFP.ForStmt)
forLoopBodyToSimpleForProgram body = do
    (bools, stmt) <- collectBooleans body
    stmt' <- stmtToSimpleForStmt stmt
    return (reverse bools, stmt')


stmtToSimpleForStmt :: (Show t) => FP.Stmt String t -> TSFPMonad SFP.ForStmt
stmtToSimpleForStmt (FP.SBReturn _ _) = throwError ReturnStatement
stmtToSimpleForStmt (FP.SOReturn _ _) = throwError ReturnStatement
stmtToSimpleForStmt (FP.SYield (OConst (CChar c _) _) _) = return $ SFP.PrintLbl c
stmtToSimpleForStmt (FP.SYield (OVar v _) _) = do 
    pos <- getPosition v
    return $ SFP.PrintPos pos
stmtToSimpleForStmt (FP.SYield _ _) = throwError YieldNonCharOrVar
stmtToSimpleForStmt (FP.SLetBoolean _ _ _) = throwError LetBindingBoolean
stmtToSimpleForStmt (FP.SLetOutput _ _ _ _) = throwError LetBindingOExpression
stmtToSimpleForStmt (FP.SSetTrue v _) = return $ SFP.SetTrue (BName v)
stmtToSimpleForStmt (FP.SSeq ss _) = do
    ss' <- mapM stmtToSimpleForStmt ss
    return $ SFP.Seq ss'
stmtToSimpleForStmt (FP.SIf c t e _) = do
    c' <- bExprToSimpleForBExpr c
    t' <- stmtToSimpleForStmt t
    e' <- stmtToSimpleForStmt e
    return $ SFP.If c' t' e'
stmtToSimpleForStmt (FP.SFor dir (i, e, _) (OVar v _) s _) = do 
    let dir' = case dir of
            FP.Forward -> SFP.LeftToRight
            FP.Backward -> SFP.RightToLeft
    withPosition i e $ do
        (bs, s') <- forLoopBodyToSimpleForProgram s
        return $ SFP.For (PName i) dir' bs s'
stmtToSimpleForStmt (FP.SFor _ _ v _ _) = do
    traceM $ "Iterating over " ++ show v
    throwError IteratorOverNonVariable

bExprToSimpleForBExpr :: (Show t) => FP.BExpr String t -> TSFPMonad SFP.BoolExpr
bExprToSimpleForBExpr (FP.BConst b _) = return $ SFP.BConst b
bExprToSimpleForBExpr (FP.BVar v _) = return $ SFP.BVar (BName v)
bExprToSimpleForBExpr (FP.BComp op (PVar p1 _) (PVar p2 _) _) = return $ SFP.BTest op (PName p1) (PName p2)
bExprToSimpleForBExpr (FP.BNot b _) = SFP.BNot <$> bExprToSimpleForBExpr b
bExprToSimpleForBExpr (FP.BOp op b1 b2 _) = SFP.BBin op <$> bExprToSimpleForBExpr b1 <*> bExprToSimpleForBExpr b2
bExprToSimpleForBExpr (FP.BGen _ _) = throwError GeneratorExpression
bExprToSimpleForBExpr (FP.BApp _ _ _) = throwError FunctionCall
bExprToSimpleForBExpr (FP.BLitEq _ (CChar c _) (OVar v _) _) = do
    pos <- getPosition v
    return $ SFP.BLabelAt pos c
bExprToSimpleForBExpr (FP.BLitEq _ _ _ _) = throwError LiteralEqualityTest

