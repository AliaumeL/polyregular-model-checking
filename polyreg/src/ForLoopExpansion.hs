{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForLoopExpansion where

-- In this module, we expand for loops
-- on generators, so that the *only* for loops
-- that exist are on variables or reverse variables.

import QuantifierFree
import ForPrograms
import ForProgramsTyping (ValueType(..),OutputType(..))
import ForProgramsPrettyPrint (prettyPrintStmtWithNls, prettyPrintProgramWithNls)

import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M

import AddrVarElimination (StmtZip(..), ExtVars(..), eliminateExtVarsProg, reverseStmtZip)

import Debug.Trace

emptyStmt :: t -> Stmt v t
emptyStmt t = SSeq [] t
--emptyStmt t = SYield (OConst (CList [] t) t) t

class Monad m => MonadForElim m where
    withVar       :: String -> m a -> m a
    getVar        :: String -> m (ExtVars String ValueType)
    getVarOrSame  :: String -> m (ExtVars String ValueType)
    freshVar      :: String -> m String

    throwWithCtx  :: String -> m a
    guardOrThrow  :: Bool   -> String -> m ()

data ForElimState = ForElimState {
    varMap   :: Map String String,        -- remapping of variables
    counter  :: Int                       -- unique counter
} deriving (Eq, Show)

data ForElimError = ForElimError String
    deriving (Eq, Show)


newtype ForElim a = ForElim (ExceptT ForElimError (State ForElimState) a)
    deriving (Functor, Applicative, Monad, MonadError ForElimError, MonadState ForElimState)


runForElim :: ForElim a -> Either ForElimError a
runForElim (ForElim m) = evalState (runExceptT m) (ForElimState M.empty 0)

-- replaceHashPart "a#..." 13 = "a#13"
-- replaceHashPart "abc" 123 = "abc#123"
replaceHashPart :: Int -> String -> String
replaceHashPart i s = case break (=='#') s of
    (a, '#':b) -> a ++ "#for-exp#" ++ s ++ "#" ++ show i
    (a, b)     -> a ++ "#for-exp#" ++ s ++ "#" ++ show i


instance MonadForElim ForElim where
    withVar v m = do
        count  <- gets counter
        oldMap <- gets varMap
        modify $ \s -> s { counter = count + 1 , varMap = M.insert v (replaceHashPart count v) oldMap }
        result <- m
        modify $ \s -> s { varMap = oldMap }
        return result
    getVarOrSame v = do
        m <- gets varMap
        case M.lookup v m of
            Nothing -> return $ (OldVar v)
            Just v' -> return $ (OldVar v')
    getVar v = do
        m <- gets varMap
        case M.lookup v m of
            Just v' -> return $ OldVar v'
            Nothing -> throwWithCtx $ "getVar: variable not found " ++ v

    freshVar v = do
        count <- gets counter
        modify $ \s -> s { counter = count + 1 }
        return $ replaceHashPart count v

    throwWithCtx s   = throwError $ ForElimError s
    guardOrThrow b s = unless b $ throwWithCtx s


-- Reverses all the generators (and checks that they are only on variables)
-- removes all "letBool" and "setTrue" statements,
-- and turns `ifs` into sequences.
reverseAndSimplify :: (Show v, Show t) => Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
reverseAndSimplify (SYield o t) = SYield o t
reverseAndSimplify (SOReturn (OConst (CList [] _) _) t) = emptyStmt t
reverseAndSimplify (SOReturn _ _) = error "SOReturn in reverseAndSimplify"
reverseAndSimplify (SBReturn _ _) = error "SBReturn in reverseAndSimplify"
reverseAndSimplify (SIf _ s1 s2 t) = SSeq [reverseAndSimplify s2, reverseAndSimplify s1] t
reverseAndSimplify (SLetOutput _ _ _ _) = error "SLetOutput in reverseAndSimplify"
reverseAndSimplify (SLetBoolean _ s t) = reverseAndSimplify s
reverseAndSimplify (SSetTrue _ t) = emptyStmt t
reverseAndSimplify (SSeq ss t) = SSeq (reverse $ map reverseAndSimplify ss) t
reverseAndSimplify (SFor dir (OldVar i, OldVar e, t) v body t'') = simplified
    where
        body' = reverseAndSimplify body
        simplified = SFor (reverseDirection dir) (OldVar i, OldVar e, t) v body' t''
reverseAndSimplify s@(SFor _ _ _ _ _) = error $ "SFor in reverseAndSimplify" ++ show s




refreshBooleanVariablesStmt :: (MonadForElim m) =>
                               Stmt (ExtVars String ValueType) ValueType ->
                               m (Stmt (ExtVars String ValueType) ValueType)
refreshBooleanVariablesStmt (SYield o t) = return $ SYield o t
refreshBooleanVariablesStmt (SOReturn o t) = return $ SOReturn o t
refreshBooleanVariablesStmt (SBReturn b t) = SBReturn <$> (refreshBooleanVariablesBExpr b) <*> pure t
refreshBooleanVariablesStmt (SIf b s1 s2 t) = SIf <$> (refreshBooleanVariablesBExpr b)
                                                    <*> (refreshBooleanVariablesStmt s1)
                                                    <*> (refreshBooleanVariablesStmt s2)
                                                    <*> (pure t)
refreshBooleanVariablesStmt (SLetOutput v o s t) = SLetOutput v o
                                                              <$> (refreshBooleanVariablesStmt s)
                                                              <*> (pure t)
refreshBooleanVariablesStmt (SLetBoolean (OldVar v) s t) = withVar v $ do
    newNameV <- getVar v
    s' <- refreshBooleanVariablesStmt s
    return $ SLetBoolean newNameV s' t
refreshBooleanVariablesStmt (SSetTrue (OldVar v) t) = do
    v' <- getVar v
    return $ SSetTrue v' t
refreshBooleanVariablesStmt (SFor dir (OldVar i, OldVar e, t) o s t') = SFor dir (OldVar i, OldVar e, t) o <$> refreshBooleanVariablesStmt s <*> pure t'
refreshBooleanVariablesStmt (SSeq ss t) = SSeq <$> mapM refreshBooleanVariablesStmt ss <*> pure t
refreshBooleanVariablesStmt x = error $ "invalid statement in refreshBooleanVariablesStmt " ++ show x
    

refreshBooleanVariablesBExpr :: (MonadForElim m) =>
                                BExpr (ExtVars String ValueType) ValueType ->
                                m (BExpr (ExtVars String ValueType) ValueType)
refreshBooleanVariablesBExpr (BConst b t) = return $ BConst b t
refreshBooleanVariablesBExpr (BNot b t) = BNot <$> refreshBooleanVariablesBExpr b <*> pure t
refreshBooleanVariablesBExpr (BOp op b1 b2 t) = BOp op <$> refreshBooleanVariablesBExpr b1 <*> refreshBooleanVariablesBExpr b2 <*> pure t
refreshBooleanVariablesBExpr (BComp comp p1 p2 t) = return $ BComp comp p1 p2 t
refreshBooleanVariablesBExpr (BVar (OldVar v) t) = do
    v' <- getVar v
    return $ BVar v' t
refreshBooleanVariablesBExpr (BVar v t) = error $ "BVar in refreshBooleanVariablesBExpr " ++ show v
refreshBooleanVariablesBExpr (BGen s t) = return $ BGen s t -- we do not go inside generators
refreshBooleanVariablesBExpr (BApp _ _ _) = throwWithCtx "BApp in refreshBooleanVariablesBExpr"
refreshBooleanVariablesBExpr ans@(BLitEq t c o t') = return ans



forLoopExpansion :: Program String ValueType -> Either ForElimError (Program String ValueType)
forLoopExpansion x = let z = (forLoopExpansionProg  (mapVarsProgram OldVar x)) in
                     --let z' = (fmap (mapVarsProgram show)) z in  
                     fmap eliminateExtVarsProg z
forLoopExpansionProg :: Program (ExtVars String ValueType) ValueType -> Either ForElimError (Program (ExtVars String ValueType) ValueType)
forLoopExpansionProg p = runForElim (forLoopExpansionProgM p)



forLoopExpansionProgM :: (MonadForElim m) =>
                         Program (ExtVars String ValueType) ValueType ->
                         m (Program (ExtVars String ValueType) ValueType)
forLoopExpansionProgM (Program fs m) = do
    fs' <- mapM forLoopExpansionFunM fs
    return $ Program fs' m

forLoopExpansionFunM :: (MonadForElim m) =>
                        StmtFun (ExtVars String ValueType) ValueType ->
                        m (StmtFun (ExtVars String ValueType) ValueType)
forLoopExpansionFunM (StmtFun v args s t) = do
    traceM $ "Expanding for loop in function " ++ show v
    s' <- forLoopExpansionStmtM s
    return $ StmtFun v args s' t


forLoopExpansionStmtM :: (MonadForElim m) =>
                         Stmt (ExtVars String ValueType) ValueType ->
                         m (Stmt (ExtVars String ValueType) ValueType)
forLoopExpansionStmtM (SYield o t) = do
    o' <- forLoopExpansionOExprM o
    return $ SYield o' t
forLoopExpansionStmtM (SOReturn o t) = do
    o' <- forLoopExpansionOExprM o
    return $ SOReturn o' t
forLoopExpansionStmtM (SBReturn b t) = do
    b' <- forLoopExpansionBExprM b
    return $ SBReturn b' t
forLoopExpansionStmtM (SIf b s1 s2 t) = do
    b'  <- forLoopExpansionBExprM b
    s1' <- forLoopExpansionStmtM s1
    s2' <- forLoopExpansionStmtM s2
    return $ SIf b' s1' s2' t
forLoopExpansionStmtM (SLetOutput _ _ _ _) = throwWithCtx "SLetOutput in forLoopExpansionStmtM"
forLoopExpansionStmtM (SLetBoolean v s t) = do 
    s' <- forLoopExpansionStmtM s
    return $ SLetBoolean v s' t
forLoopExpansionStmtM (SSetTrue v t) = return $ SSetTrue v t
forLoopExpansionStmtM (SFor _ _ (OConst (CList [] _) _) _ t) = return $ emptyStmt t
forLoopExpansionStmtM (SFor Forward (OldVar i, OldVar e, _) (OGen stmt _) body _) = do
    traceM "Here!!!"
    stmtRefreshedFors <- refreshForLoopsStmt stmt
    stmtRefreshedBools <- refreshBooleanVariablesStmt stmtRefreshedFors
    stmt' <- forLoopExpansionStmtM stmtRefreshedBools
    body' <- forLoopExpansionStmtM body
    --traceM $ "Expanding for loop. Generator stmt:\n " ++ prettyPrintStmtWithNls 0 (mapVarsStmt show stmt') 
    --traceM $ "Expanding for loop. Body stmt:\n " ++ prettyPrintStmtWithNls 0 (mapVarsStmt show body')
    let expansion = substituteYieldStmts AddrVar i e body' stmt'
    return expansion
forLoopExpansionStmtM (SFor Backward (OldVar i, OldVar e, _) (OGen stmt _) body t) = do
    traceM "Here, but backward!!!"
    body'  <- forLoopExpansionStmtM body
    stmtRefreshedFors <- refreshForLoopsStmt stmt
    stmtRefreshedBools  <- refreshBooleanVariablesStmt stmtRefreshedFors
    stmt' <- forLoopExpansionStmtM stmtRefreshedBools
    newVar <- freshVar i
    let stmtRevSimpl = reverseAndSimplify stmt' 
    stmtRevSimpl' <- refreshForLoopsStmt stmtRevSimpl
    let guardedBody = (SIf (BComp Eq (PVar (OldVar i) t)
                                        (PVar (OldVar newVar) t) t)
                            body' 
                            (emptyStmt t) t)
    let expanded    = substituteYieldStmts AddrVar    i       e guardedBody stmt'
    let expandedRev = substituteYieldStmts AddrRevVar newVar  e expanded stmtRevSimpl'
    return expandedRev
forLoopExpansionStmtM (SFor dir (OldVar i, OldVar e, t) (OVar (OldVar v) t') body t'') = do
    body' <- forLoopExpansionStmtM body
    --v'    <- getVarOrSame v
    return $ SFor dir (OldVar i, OldVar e, t) (OVar (OldVar v) t') body' t''
forLoopExpansionStmtM (SFor dir (OldVar i, OldVar e, t) (OVar _ t') body t'') = error "SFor in forLoopExpansionStmtM"
forLoopExpansionStmtM (SSeq ss t) = do
    ss' <- mapM forLoopExpansionStmtM ss
    return $ SSeq ss' t
forLoopExpansionStmtM x = throwWithCtx $ "invalid statement in forLoopExpansionStmtM " ++ show x


forLoopExpansionOExprM :: (MonadForElim m) =>
                          OExpr (ExtVars String ValueType) ValueType ->
                          m (OExpr (ExtVars String ValueType) ValueType)
forLoopExpansionOExprM o@(OVar _ _)   = return o
forLoopExpansionOExprM c@(OConst _ _) = return c
forLoopExpansionOExprM (OList os t) = do
    os' <- mapM forLoopExpansionOExprM os
    return $ OList os' t
forLoopExpansionOExprM (OApp _ _ _) = throwWithCtx "OApp in forLoopExpansionOExprM"
forLoopExpansionOExprM (OGen s t) = do
    s' <- forLoopExpansionStmtM s
    return $ OGen s' t

forLoopExpansionBExprM :: (MonadForElim m) =>
                         BExpr (ExtVars String ValueType) ValueType ->
                         m (BExpr (ExtVars String ValueType) ValueType)
forLoopExpansionBExprM (BConst b t) = return $ BConst b t
forLoopExpansionBExprM (BNot b t) = do
    b' <- forLoopExpansionBExprM b
    return $ BNot b' t
forLoopExpansionBExprM (BOp op b1 b2 t) = do
    b1' <- forLoopExpansionBExprM b1
    b2' <- forLoopExpansionBExprM b2
    return $ BOp op b1' b2' t
forLoopExpansionBExprM (BComp op e1 e2 t) = return $ BComp op e1 e2 t
forLoopExpansionBExprM (BVar v t) = return $ BVar v t
forLoopExpansionBExprM (BVar v t) = error $ "BVar in forLoopExpansionBExprM " ++ show v
forLoopExpansionBExprM (BGen s t) = do
    s' <- forLoopExpansionStmtM s
    return $ BGen s' t
forLoopExpansionBExprM (BApp _ _ _) = throwWithCtx "BApp in forLoopExpansionBExprM"
forLoopExpansionBExprM (BLitEq t c o t') = do
    o' <- forLoopExpansionOExprM o
    return $ BLitEq t c o' t'

substituteYieldStmts :: (Show v, Show t, Eq v, Eq t) =>  
                        ((StmtZip v t) -> ExtVars v t) ->
                        v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
substituteYieldStmts cstr i e body statement = subYieldStmt cstr ZBegin i e body statement

-- subYieldStmt addr i e body statement -> expanded statement
subYieldStmt :: (Show v, Show t, Eq v, Eq t) => 
                ((StmtZip v t) -> ExtVars v t) ->
                StmtZip v t -> v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
subYieldStmt cstr z v1 v2 s (SYield o t) = substOVarStmt cstr (ForParams v1 v2 o (reverseStmtZip z)) s
subYieldStmt _    _ _ _ _   (SOReturn (OConst (CList [] _) _) t) = emptyStmt t
subYieldStmt _    _ _ _ _   (SOReturn o t) = error "SOReturn in subYield"
subYieldStmt _    _ _ _ _   (SBReturn b t) = error "SBReturn in subYield"
subYieldStmt cstr z v1 v2 s (SIf b s1 s2 t) = SIf b (subYieldStmt cstr zleft v1 v2 s s1) (subYieldStmt cstr zright v1 v2 s s2) t
    where
        zleft  = ZIfL z
        zright = ZIfR z
subYieldStmt _    _ _ _ _   (SLetOutput _ _ _ _) = error "SLetOutput in subYield"
subYieldStmt cstr z v1 v2 s (SLetBoolean v s' t) = SLetBoolean v (subYieldStmt cstr z v1 v2 s s') t
subYieldStmt _    _ _ _ _ x@(SSetTrue _ _) = x
subYieldStmt cstr z v1 v2 s (SFor dir (OldVar i, OldVar e, t) v s' t') = SFor dir (OldVar i, OldVar e, t) v (subYieldStmt cstr (ZFor dir i t z) v1 v2 s s') t'
subYieldStmt cstr z v1 v2 s (SSeq ss t) = SSeq [ subYieldStmt cstr (ZSeq i (length ss - 1) z) v1 v2 s s' | (i, s') <- zip [0..] ss ] t
subYieldStmt _    _ _ _ _ _ = error "subYieldStmt: invalid statement"



data ForParams v t = ForParams {
    forIndexVar  :: v,
    forDataVar   :: v,
    forDataExpr  :: OExpr (ExtVars v t) t,
    forIndexAddr :: StmtZip v t
} deriving (Eq,Show)


substOVarStmt :: (Eq v) => 
                 ((StmtZip v t) -> ExtVars v t) ->
                 ForParams v t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
substOVarStmt cstr p (SYield o' t) = SYield (substOVarOExpr cstr p o') t
substOVarStmt cstr p (SOReturn (OConst (CList [] _) _) t) = emptyStmt t
substOVarStmt cstr _ (SOReturn _ _) = error "SOReturn in substOVarStmt"
substOVarStmt cstr _ (SBReturn _ _) = error "SBReturn in substOVarStmt"
substOVarStmt cstr p (SIf b s1 s2 t) = SIf (substOVarBExpr cstr p b) (substOVarStmt cstr p s1) (substOVarStmt cstr p s2) t
substOVarStmt cstr _ (SLetOutput _ _ _ _) = error "SLetOutput in substOVarStmt"
substOVarStmt cstr p (SLetBoolean v' s t) = SLetBoolean v' (substOVarStmt cstr p s) t
substOVarStmt cstr p (SSetTrue v' t) = SSetTrue v' t
substOVarStmt cstr p (SFor dir (i, e, t) v' s t') = SFor dir (i, e, t) (substOVarOExpr cstr p v') (substOVarStmt cstr p s) t'
substOVarStmt cstr p (SSeq ss t) = SSeq (map (substOVarStmt cstr p) ss) t


substOVarOExpr :: (Eq v) => 
                 ((StmtZip v t) -> ExtVars v t) ->
                  ForParams v t -> OExpr (ExtVars v t) t -> OExpr (ExtVars v t) t
substOVarOExpr cstr p (OVar (OldVar v') t) | forDataVar p == v' = forDataExpr p
substOVarOExpr cstr p (OVar v' t) = OVar v' t
substOVarOExpr cstr _ (OConst c t) = OConst c t
substOVarOExpr cstr _ (OList _ _) = error "OList in substOVarOExpr"
substOVarOExpr cstr _ (OApp _ _ _) = error "OApp in substOVarOExpr"
substOVarOExpr cstr p (OGen s t) = OGen (substOVarStmt cstr p s) t

substOVarBExpr :: (Eq v) => 
                  ((StmtZip v t) -> ExtVars v t) ->
                  ForParams v t -> BExpr (ExtVars v t) t -> BExpr (ExtVars v t) t
substOVarBExpr cstr p (BConst b t) = BConst b t
substOVarBExpr cstr p (BNot b t) = BNot (substOVarBExpr cstr p b) t
substOVarBExpr cstr p (BOp op b1 b2 t) = BOp op (substOVarBExpr cstr p b1) (substOVarBExpr cstr p b2) t
substOVarBExpr cstr p (BComp comp p1 p2 t) = BComp comp (substOVarPExpr cstr p p1) (substOVarPExpr cstr p p2) t
substOVarBExpr cstr p (BVar v' t) = BVar v' t
substOVarBExpr cstr p (BGen s t) = BGen (substOVarStmt cstr p s) t
substOVarBExpr cstr p (BApp _ _ _) = error "BApp in substOVarBExpr"
substOVarBExpr cstr p (BLitEq t c o t') = BLitEq t c (substOVarOExpr cstr p o) t'

substOVarPExpr :: (Eq v) =>
                  ((StmtZip v t) -> ExtVars v t) ->
                  ForParams v t -> PExpr (ExtVars v t) t -> PExpr (ExtVars v t) t
substOVarPExpr cstr p (PVar (OldVar v) t) | forIndexVar p == v = PVar (cstr (forIndexAddr p)) t
substOVarPExpr cstr p (PVar v t) = PVar v t



remapVariable :: (Eq v, Eq t) => v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
remapVariable old new s = mapVarsStmt f s
    where
        f v | v == (OldVar old)  = (OldVar new)
            | otherwise = v


type ExStr = ExtVars String ValueType

refreshForLoopsStmt :: (MonadForElim m) => Stmt ExStr ValueType -> m (Stmt ExStr ValueType)
refreshForLoopsStmt (SYield o t)   = SYield <$> (refreshForLoopsOExpr o)   <*> pure t
refreshForLoopsStmt (SOReturn o t) = SOReturn <$> (refreshForLoopsOExpr o) <*> pure t
refreshForLoopsStmt (SBReturn b t) = SBReturn <$> (refreshForLoopsBExpr b) <*> pure t
refreshForLoopsStmt (SIf b s1 s2 t) = SIf <$> (refreshForLoopsBExpr b)
                                          <*> (refreshForLoopsStmt s1)
                                          <*> (refreshForLoopsStmt s2)
                                          <*> (pure t)
refreshForLoopsStmt (SLetOutput v o s t) = SLetOutput v <$> (refreshForLoopsOExpr o) 
                                                        <*> (refreshForLoopsStmt s)
                                                        <*> (pure t)
refreshForLoopsStmt (SLetBoolean v s t) = SLetBoolean v <$> (refreshForLoopsStmt s) 
                                                        <*> (pure t)
refreshForLoopsStmt (SSetTrue v t) = return $ SSetTrue v t
refreshForLoopsStmt (SFor dir (OldVar i, OldVar e, t) o s t') = do
    withVar i $ do
        withVar e $ do
            i' <- getVar i
            e' <- getVar e
            o' <- refreshForLoopsOExpr o
            s' <- refreshForLoopsStmt s
            return $ SFor dir (i', e', t) o' s' t'
refreshForLoopsStmt (SSeq ss t) = SSeq <$> mapM refreshForLoopsStmt ss <*> pure t
refreshForLoopsStmt x = error $ "invalid statement in refreshForLoopsStmt " ++ show x

refreshForLoopsOExpr :: (MonadForElim m) => OExpr ExStr ValueType -> m (OExpr ExStr ValueType)
refreshForLoopsOExpr (OVar (OldVar v) t) = do
    v' <- getVarOrSame v
    return $ OVar v' t
refreshForLoopsOExpr (OVar v t) = return $ OVar v t
refreshForLoopsOExpr (OConst c t) = return $ OConst c t
refreshForLoopsOExpr (OList os t) = OList <$> mapM refreshForLoopsOExpr os <*> pure t
refreshForLoopsOExpr (OApp _ _ _) = throwWithCtx "OApp in refreshForLoopsOExpr"
refreshForLoopsOExpr (OGen s t) = OGen <$> refreshForLoopsStmt s <*> pure t

refreshForLoopsBExpr :: (MonadForElim m) => BExpr ExStr ValueType -> m (BExpr ExStr ValueType)
refreshForLoopsBExpr (BConst b t) = return $ BConst b t
refreshForLoopsBExpr (BNot b t) = BNot <$> refreshForLoopsBExpr b <*> pure t
refreshForLoopsBExpr (BOp op b1 b2 t) = BOp op <$> refreshForLoopsBExpr b1 <*> refreshForLoopsBExpr b2 <*> pure t
refreshForLoopsBExpr (BComp comp p1 p2 t) = BComp comp <$> refreshForLoopsPExpr p1 <*> refreshForLoopsPExpr p2 <*> pure t
refreshForLoopsBExpr (BVar v t) = return $ BVar v t
refreshForLoopsBExpr (BGen s t) = BGen <$> refreshForLoopsStmt s <*> pure t
refreshForLoopsBExpr (BApp _ _ _) = throwWithCtx "BApp in refreshForLoopsBExpr"
refreshForLoopsBExpr (BLitEq t c o t') = BLitEq t c <$> refreshForLoopsOExpr o <*> pure t'

refreshForLoopsPExpr :: (MonadForElim m) => PExpr ExStr ValueType -> m (PExpr ExStr ValueType)
refreshForLoopsPExpr (PVar (OldVar v) t) = PVar <$> getVarOrSame v <*> pure t
-- trace ("refresh-for-loop: " ++ show v) $ return $ PVar (OldVar v) t
refreshForLoopsPExpr (PVar v t) = trace (show v) $ return $ PVar v t


hasForLoopOverGenProgram :: Program s t -> Bool
hasForLoopOverGenProgram (Program fs _) = any hasForLoopOverGenFun fs

hasForLoopOverGenFun :: StmtFun s t -> Bool
hasForLoopOverGenFun (StmtFun _ _ s _) = hasForLoopOverGenStmt s

hasForLoopOverGenStmt :: Stmt s t -> Bool
hasForLoopOverGenStmt (SFor _ _ (OGen _ _) _ _) = True
hasForLoopOverGenStmt (SFor _ _ e s _) = hasForLoopOverGenStmt s || hasForLoopOverGenOExpr e
hasForLoopOverGenStmt (SSeq ss _) = any hasForLoopOverGenStmt ss
hasForLoopOverGenStmt (SIf b s1 s2 _) = hasForLoopOverGenStmt s1 || hasForLoopOverGenStmt s2 || hasForLoopOverGenBExpr b
hasForLoopOverGenStmt (SLetBoolean _ s _) = hasForLoopOverGenStmt s
hasForLoopOverGenStmt (SLetOutput _ e s _) = hasForLoopOverGenStmt s || hasForLoopOverGenOExpr e
hasForLoopOverGenStmt (SYield o _) = hasForLoopOverGenOExpr o
hasForLoopOverGenStmt (SOReturn o _) = hasForLoopOverGenOExpr o
hasForLoopOverGenStmt (SBReturn b _) = hasForLoopOverGenBExpr b
hasForLoopOverGenStmt _ = False

hasForLoopOverGenOExpr :: OExpr s t -> Bool
hasForLoopOverGenOExpr (OGen s _) = hasForLoopOverGenStmt s
hasForLoopOverGenOExpr (OApp _ args _) = any hasForLoopOverGenOExpr args'
    where args' = map fst args
hasForLoopOverGenOExpr (OList os _) = any hasForLoopOverGenOExpr os
hasForLoopOverGenOExpr _ = False

hasForLoopOverGenBExpr :: BExpr s t -> Bool
hasForLoopOverGenBExpr (BGen stmt _) = hasForLoopOverGenStmt stmt
hasForLoopOverGenBExpr (BOp _ b1 b2 _) = hasForLoopOverGenBExpr b1 || hasForLoopOverGenBExpr b2
hasForLoopOverGenBExpr _ = False

-- This works in the for-loop expansion monad 
forLoopExpansionFixM :: (MonadForElim m) => Program String ValueType -> m (Program String ValueType)
forLoopExpansionFixM p 
    | hasForLoopOverGenProgram p = do
        p' <- forLoopExpansionProgM $ mapVarsProgram OldVar p
        let p'' = eliminateExtVarsProg p' 
        forLoopExpansionFixM p''
    | otherwise = return p

forLoopExpansionFix :: Program String ValueType -> Either ForElimError (Program String ValueType)
forLoopExpansionFix p = runForElim (forLoopExpansionFixM p)