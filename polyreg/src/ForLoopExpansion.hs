{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForLoopExpansion where

-- In this module, we expand for loops
-- on generators, so that the *only* for loops
-- that exist are on variables or reverse variables.

import QuantifierFree
import ForPrograms
import ForProgramsTyping (ValueType(..))
import ForProgramsPrettyPrint (prettyPrintStmtWithNls, prettyPrintProgramWithNls)

import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as M

import AddrVarElimination (StmtZip(..), ExtVars(..), eliminateExtVarsProg, reverseStmtZip)

import Debug.Trace

-- Reverses all the generators (and checks that they are only on variables)
-- removes all "letBool" and "setTrue" statements,
-- and turns `ifs` into sequences.
reverseAndSimplify :: Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
reverseAndSimplify (SYield o t) = SYield o t
reverseAndSimplify (SOReturn _ _) = error "SOReturn in reverseAndSimplify"
reverseAndSimplify (SBReturn _ _) = error "SBReturn in reverseAndSimplify"
reverseAndSimplify (SIf _ s1 s2 t) = SSeq [reverseAndSimplify s1, reverseAndSimplify s2] t
reverseAndSimplify (SLetOutput _ _ _ _) = error "SLetOutput in reverseAndSimplify"
reverseAndSimplify (SLetBoolean _ s t) = reverseAndSimplify s
reverseAndSimplify (SSetTrue _ t) = SSeq [] t
reverseAndSimplify (SSeq ss t) = SSeq (map reverseAndSimplify ss) t
reverseAndSimplify (SFor (OldVar i, OldVar e, t) (OVar v t') body t'') = simplified
    where
        body' = reverseAndSimplify body
        simplified = SFor (OldVar i, OldVar e, t) (ORev (OVar v t') t') body' t''
reverseAndSimplify (SFor (OldVar i, OldVar e, t) (ORev oexpr t') body t'') = simplified
    where
        body' = reverseAndSimplify body
        simplified = SFor (OldVar i, OldVar e, t) oexpr body' t''
reverseAndSimplify (SFor _ _ _ _) = error "SFor in reverseAndSimplify"


forLoopExpansion :: Program String ValueType -> Either ForElimError (Program String ValueType)
forLoopExpansion x = let z = (forLoopExpansionProg  (mapVarsProgram OldVar x)) in
                     let z' = (fmap (mapVarsProgram show)) z in  
                     trace (either show prettyPrintProgramWithNls z') $ fmap eliminateExtVarsProg z
forLoopExpansionProg :: Program (ExtVars String ValueType) ValueType -> Either ForElimError (Program (ExtVars String ValueType) ValueType)
forLoopExpansionProg p = runForElim (forLoopExpansionProgM p)


class Monad m => MonadForElim m where
    withVar       :: String -> m a -> m a
    getVar        :: String -> m (ExtVars String ValueType)
    getVarMaybe   :: String -> m (Maybe (ExtVars String ValueType))
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
    getVarMaybe v = do
        m <- gets varMap
        return . fmap OldVar $ M.lookup v m
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
forLoopExpansionStmtM (SLetBoolean (OldVar v) s t) = withVar v $ do
    newNameV <- getVar v
    s' <- forLoopExpansionStmtM s
    return $ SLetBoolean newNameV s' t
forLoopExpansionStmtM (SSetTrue (OldVar v) t) = do
    v' <- getVar v
    return $ SSetTrue v' t
forLoopExpansionStmtM (SFor (OldVar i, OldVar e, _) (OGen stmt _) body _) = do
    body' <- forLoopExpansionStmtM body
    stmt' <- forLoopExpansionStmtM stmt
    --traceM $ "Expanding for loop. Generator stmt:\n " ++ prettyPrintStmtWithNls 0 (mapVarsStmt show stmt') 
    --traceM $ "Expanding for loop. Body stmt:\n " ++ prettyPrintStmtWithNls 0 (mapVarsStmt show body')
    let expansion = substituteYieldStmts i e body' stmt'
    return expansion
forLoopExpansionStmtM (SFor (OldVar i, OldVar e, _) (ORev (OGen stmt _) _) body t) = do
    body'  <- forLoopExpansionStmtM body
    stmt'  <- forLoopExpansionStmtM stmt
    newVar <- freshVar i
    let stmtRevSimpl = reverseAndSimplify stmt' 
    stmtRevSimpl' <- refreshForLoopsStmt stmtRevSimpl
    trace ("Variables " ++ show [i,e,newVar]) $
        trace (prettyPrintStmtWithNls 0 (mapVarsStmt show stmt')) $ 
            trace (prettyPrintStmtWithNls 0 (mapVarsStmt show stmtRevSimpl')) $ do
                let guardedBody = (SIf (BComp Eq (PVar (OldVar i) t)
                                                 (PVar (OldVar newVar) t) t)
                                        body' 
                                        (SSeq [] t) t)
                let expanded    = substituteYieldStmts i       e guardedBody stmt'
                let expandedRev = substituteYieldStmts newVar  e expanded    stmtRevSimpl'
                trace (prettyPrintStmtWithNls 0 (mapVarsStmt show expandedRev)) $
                    return expandedRev
forLoopExpansionStmtM (SFor (OldVar i, OldVar e, t) (OVar v t') body t'') = do
    body' <- forLoopExpansionStmtM body
    return $ SFor (OldVar i, OldVar e, t) (OVar v t') body' t''
forLoopExpansionStmtM (SFor (OldVar i, OldVar e, t) (ORev (OVar v t') t'') body t''') = do
    body' <- forLoopExpansionStmtM body
    return $ SFor (OldVar i, OldVar e, t) (ORev (OVar v t') t'') body' t'''
forLoopExpansionStmtM (SFor (OldVar i, OldVar e, t) (ORev (ORev o _) _) body t') = do
    body' <- forLoopExpansionStmtM body
    return $ SFor (OldVar i, OldVar e, t) o body' t'
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
forLoopExpansionOExprM (ORev o t) = do
    o' <- forLoopExpansionOExprM o
    return $ ORev o' t
forLoopExpansionOExprM (OIndex o p t) = do
    o' <- forLoopExpansionOExprM o
    return $ OIndex o' p t
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
forLoopExpansionBExprM (BVar (OldVar v) t) = do
    v' <- getVar v
    return $ BVar v' t
forLoopExpansionBExprM (BVar v t) = error $ "BVar in forLoopExpansionBExprM " ++ show v
forLoopExpansionBExprM (BGen s t) = do
    s' <- forLoopExpansionStmtM s
    return $ BGen s' t
forLoopExpansionBExprM (BApp _ _ _) = throwWithCtx "BApp in forLoopExpansionBExprM"
forLoopExpansionBExprM (BLitEq t c o t') = do
    o' <- forLoopExpansionOExprM o
    return $ BLitEq t c o' t'

substituteYieldStmts :: (Show v, Show t, Eq v, Eq t) =>  v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
substituteYieldStmts i e body statement = subYieldStmt ZBegin i e body statement

-- subYieldStmt addr i e body statement -> expanded statement
subYieldStmt :: (Show v, Show t, Eq v, Eq t) => StmtZip v t -> v -> v -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
subYieldStmt z v1 v2 s (SYield o t) = substOVarStmt (ForParams v1 v2 o (reverseStmtZip z)) s
subYieldStmt _ _ _ _   (SOReturn o t) = error "SOReturn in subYield"
subYieldStmt _ _ _ _   (SBReturn b t) = error "SBReturn in subYield"
subYieldStmt z v1 v2 s (SIf b s1 s2 t) = SIf b (subYieldStmt zleft v1 v2 s s1) (subYieldStmt zright v1 v2 s s2) t
    where
        zleft  = ZIfL z
        zright = ZIfR z
subYieldStmt _ _ _ _   (SLetOutput _ _ _ _) = error "SLetOutput in subYield"
subYieldStmt z v1 v2 s (SLetBoolean v s' t) = SLetBoolean v (subYieldStmt z v1 v2 s s') t
subYieldStmt _ _ _ _ x@(SSetTrue _ _) = x
subYieldStmt z v1 v2 s (SFor (OldVar i, OldVar e, t) v s' t') = SFor (OldVar i, OldVar e, t) v (subYieldStmt (ZFor i t z) v1 v2 s s') t'
subYieldStmt z v1 v2 s (SSeq ss t) = SSeq [ subYieldStmt (ZSeq i z) v1 v2 s s' | (i, s') <- zip [0..] ss ] t
subYieldStmt _ _ _ _ _ = error "subYieldStmt: invalid statement"



data ForParams v t = ForParams {
    forIndexVar  :: v,
    forDataVar   :: v,
    forDataExpr  :: OExpr (ExtVars v t) t,
    forIndexAddr :: StmtZip v t
} deriving (Eq,Show)


substOVarStmt :: (Eq v) => ForParams v t -> Stmt (ExtVars v t) t -> Stmt (ExtVars v t) t
substOVarStmt p (SYield o' t) = SYield (substOVarOExpr p o') t
substOVarStmt _ (SOReturn _ _) = error "SOReturn in substOVarStmt"
substOVarStmt _ (SBReturn _ _) = error "SBReturn in substOVarStmt"
substOVarStmt p (SIf b s1 s2 t) = SIf (substOVarBExpr p b) (substOVarStmt p s1) (substOVarStmt p s2) t
substOVarStmt _ (SLetOutput _ _ _ _) = error "SLetOutput in substOVarStmt"
substOVarStmt p (SLetBoolean v' s t) = SLetBoolean v' (substOVarStmt p s) t
substOVarStmt p (SSetTrue v' t) = SSetTrue v' t
substOVarStmt p (SFor (i, e, t) v' s t') = SFor (i, e, t) v' (substOVarStmt p s) t'
substOVarStmt p (SSeq ss t) = SSeq (map (substOVarStmt p) ss) t


substOVarOExpr :: (Eq v) => ForParams v t -> OExpr (ExtVars v t) t -> OExpr (ExtVars v t) t
substOVarOExpr p (OVar (OldVar v') t) | forDataVar p == v' = forDataExpr p
substOVarOExpr p (OVar v' t) = OVar v' t
substOVarOExpr _ (OConst c t) = OConst c t
substOVarOExpr _ (OList _ _) = error "OList in substOVarOExpr"
substOVarOExpr p (ORev o t) = ORev (substOVarOExpr p o) t
substOVarOExpr _ (OIndex _ _ _) = error "OIndex in substOVarOExpr"
substOVarOExpr _ (OApp _ _ _) = error "OApp in substOVarOExpr"
substOVarOExpr p (OGen s t) = OGen (substOVarStmt p s) t

substOVarBExpr :: (Eq v) => ForParams v t -> BExpr (ExtVars v t) t -> BExpr (ExtVars v t) t
substOVarBExpr p (BConst b t) = BConst b t
substOVarBExpr p (BNot b t) = BNot (substOVarBExpr p b) t
substOVarBExpr p (BOp op b1 b2 t) = BOp op (substOVarBExpr p b1) (substOVarBExpr p b2) t
substOVarBExpr p (BComp comp p1 p2 t) = BComp comp (substOVarPExpr p p1) (substOVarPExpr p p2) t
substOVarBExpr p (BVar v' t) = BVar v' t
substOVarBExpr p (BGen s t) = BGen (substOVarStmt p s) t
substOVarBExpr p (BApp _ _ _) = error "BApp in substOVarBExpr"
substOVarBExpr p (BLitEq t c o t') = BLitEq t c (substOVarOExpr p o) t'

substOVarPExpr :: (Eq v) => ForParams v t -> PExpr (ExtVars v t) t -> PExpr (ExtVars v t) t
substOVarPExpr p (PVar (OldVar v) t) | forIndexVar p == v = PVar (AddrVar v (forIndexAddr p)) t
substOVarPExpr p (PVar v t) = PVar v t



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
refreshForLoopsStmt (SFor (OldVar i, OldVar e, t) o s t') = do
    withVar i $ do
        withVar e $ do
            i' <- getVar i
            e' <- getVar e
            o' <- refreshForLoopsOExpr o
            s' <- refreshForLoopsStmt s
            return $ SFor (i', e', t) o' s' t'
refreshForLoopsStmt (SSeq ss t) = SSeq <$> mapM refreshForLoopsStmt ss <*> pure t
refreshForLoopsStmt x = error $ "invalid statement in refreshForLoopsStmt " ++ show x

refreshForLoopsOExpr :: (MonadForElim m) => OExpr ExStr ValueType -> m (OExpr ExStr ValueType)
refreshForLoopsOExpr (OVar (OldVar v) t) = do
    v' <- getVarMaybe v
    case v' of 
        Nothing  -> return (OVar (OldVar v) t)
        Just v'' -> return (OVar v'' t)
refreshForLoopsOExpr (OVar v t) = return $ OVar v t
refreshForLoopsOExpr (OConst c t) = return $ OConst c t
refreshForLoopsOExpr (OList os t) = OList <$> mapM refreshForLoopsOExpr os <*> pure t
refreshForLoopsOExpr (ORev o t) = ORev <$> refreshForLoopsOExpr o <*> pure t
refreshForLoopsOExpr (OIndex o p t) = OIndex <$> refreshForLoopsOExpr o <*> pure p <*> pure t
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
refreshForLoopsPExpr (PVar v t) = return $ PVar v t


    

