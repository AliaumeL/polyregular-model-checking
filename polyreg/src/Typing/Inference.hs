{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Typing.Inference where

import qualified Data.Map as M
import qualified Data.IntMap as IntMap

import qualified Typing.Constraints as C
import ForPrograms
import ForProgramsTyping (ValueType(..), OutputType(..))
import QuantifierFree

import Control.Monad
import Control.Monad.State


-- | Collect constraints from a program.
-- every variable name and every statement is given a unique number
-- we collect constraints 
--
-- [ (for (i, e) in o do s) ] => (e, Minus, o) ; ((for...), Equal, s)
-- [ if b then s1 else s2 ]   => (b, Equal, TBool) ; (s1, Equal, s2)
-- [ SSeq [s1, ..., sn] ]     => (s1, Equal, s2) ; (s2, Equal, s3) ; ... ; (sn-1, Equal, sn)
-- [ SSetTrue v ]             => (v, Equal, TBool)
-- [ SLetOutput (v, t) e s ]  => (e, Equal, v) ; ((SLetOutput ...), Equal, s)
-- [ SLetBoolean v s ]        => ((SLetBoolean ...), Equal, s); (v, Equal, TBool)
-- [ SOReturn e ]             => (e, Equal, (SOReturn ...))
-- [ SBReturn b ]             => (b, Equal, TBool) ; (SBReturn ..., Equal, TBool)
-- [ SYield e ]               => (e, Minus, (SYield ...))
--
-- [ OVar v ]                 => (v, Equal, T)
-- [ OConst c ]               => (c, Equal, T)
-- [ OList (e1,...,en) ]               => (ei, Minus, (OList ...))
-- [ ORev e ]                 => (e, Equal, (ORev ...)) 
-- [ OIndex e p ]             => (e, Equal, (OIndex ...)) ; (p, Equal, T)
-- [ OApp f args ]            => (arguments have same type)
-- [ OGen stmt ]              => (stmt, Equal, (OGen ...))
--
-- [ BBinOp op e1 e2 ]        => (e1, Equal, TBool) ; (e2, Equal, TBool) ; (SBinOp ... , Equal, TBool)
-- [ BCmpOp op e1 e2 ]        => (SCmpOp ... , Equal, TBool)
-- [ BNot e ]                 => (e, Equal, TBool)
-- [ BVar v ]                 => (v, Equal, TBool)
-- [ BGen stmt ]              => (stmt, Equal, TBool) ; (BGen ..., Equal, TBool)
-- [ BApp f args ]            => (arguments have same type)
-- [ BLitEq c e ]             => (c, Equal, e) ; (BLitEq ... , Equal, TBool)
--
-- [ CChar c ]                 => (v, Equal, TList 0)
-- [ CList (e1,...,en) ]       => (ei, Minus, (CList ...))
--
--
-- Then, we build a graph from these constraints using `createGraph`
-- and solve the constraints using `solveConstraints`
-- In case of success we have a map from every subprogram into an integer,
-- and from integers to types, so composing them leads to a fully typed program.
--

-- We assign a variable (int) to every *code point* in the program.
-- This respects variables in the original program, meaning 
-- that a variable "v" is mapped to the same int regardless of its position
-- (unless it is shadowed by a new variable with the same name).

data PosMove = PosIfL 
             | PosIfR 
             | PosIfB 
             | PosYield 
             | PosORet 
             | PosBRet 
             | PosLetOVar 
             | PosLetOExpr 
             | PosLetOStmt 
             | PosSetTrue 
             | PosLetBoolVar 
             | PosLetBoolStmt 
             | PosForVar 
             | PosForExpr 
             | PosForStmt 
             | PosSeq Int 
             | PosBNot 
             | PosBOpL | PosBOpR 
             | PosBGen 
             | PosBAppArg Int
             | PosBLitEqL 
             | PosBLitEqR 
             | PosOGen 
             | PosOConst 
             | PosOList Int
             | PosORev
             | PosOIndexL
             | PosOAppArg Int
             | PosOExprRoot
             | PosCList Int
             | PosFun String
             | PosFunBody 
             | PosFunArg  Int
             deriving (Show, Eq, Ord)

newtype Pos = Pos [PosMove] deriving (Show, Eq, Ord)


data ProgramCodePoint t = CodePointStmt    (Stmt String t)
                        | CodePointBExpr   (BExpr String t)
                        | CodePointOExpr   (OExpr String t)
                        | CodePointCExpr   (CExpr String t)
                        | CodePointFun     (StmtFun String t)
                        | CodePointProg    (Program String t)
                        | CodePointVar     String
                        deriving (Show, Eq)

outputTypeDepth :: OutputType -> Int
outputTypeDepth TOChar = 0
outputTypeDepth (TOList t) = 1 + outputTypeDepth t

depthToType :: Int -> OutputType
depthToType 0 = TOChar
depthToType n = TOList $ depthToType (n-1)

cTypeToValueType :: C.Type -> ValueType
cTypeToValueType C.TBool = TBool
cTypeToValueType (C.TList n) = TOutput . depthToType $ n

valueTypeToCType :: ValueType -> C.Type
valueTypeToCType TBool = C.TBool
valueTypeToCType (TOutput t) = C.TList $ outputTypeDepth t
valueTypeToCType (TConst t) = C.TList $ outputTypeDepth t
valueTypeToCType (TPos _) = error $ "Cannot convert TPos to CType"



posMove :: PosMove -> ProgramCodePoint t -> ProgramCodePoint t
posMove (PosIfL) (CodePointStmt (SIf _ s _ _)) = CodePointStmt s
posMove (PosIfR) (CodePointStmt (SIf _ _ s _)) = CodePointStmt s
posMove (PosIfB) (CodePointStmt (SIf b _ _ _)) = CodePointBExpr b
posMove (PosYield) (CodePointStmt (SYield e _)) = CodePointOExpr e
posMove (PosORet) (CodePointStmt (SOReturn e _)) = CodePointOExpr e
posMove (PosBRet) (CodePointStmt (SBReturn b _)) = CodePointBExpr b
posMove (PosLetOVar) (CodePointStmt (SLetOutput (v, _) _ _ _)) = CodePointVar v
posMove (PosLetOExpr) (CodePointStmt (SLetOutput _ e _ _)) = CodePointOExpr e
posMove (PosLetOStmt) (CodePointStmt (SLetOutput _ _ s _)) = CodePointStmt s
posMove (PosSetTrue) (CodePointStmt (SSetTrue v _)) = CodePointVar v
posMove (PosLetBoolVar) (CodePointStmt (SLetBoolean v _ _)) = CodePointVar v
posMove (PosLetBoolStmt) (CodePointStmt (SLetBoolean _ s _)) = CodePointStmt s
posMove (PosForVar) (CodePointStmt (SFor (v, _, _) _ _ _)) = CodePointVar v
posMove (PosForExpr) (CodePointStmt (SFor _ e _ _)) = CodePointOExpr e
posMove (PosForStmt) (CodePointStmt (SFor _ _ s _)) = CodePointStmt s
posMove (PosSeq i) (CodePointStmt (SSeq ss _)) = CodePointStmt (ss !! i)
posMove (PosBNot) (CodePointBExpr (BNot b _)) = CodePointBExpr b
posMove (PosBOpL) (CodePointBExpr (BOp _ e _ _)) = CodePointBExpr e
posMove (PosBOpR) (CodePointBExpr (BOp _ _ e _)) = CodePointBExpr e
posMove (PosBGen) (CodePointBExpr (BGen s _)) = CodePointStmt s
posMove (PosBAppArg i) (CodePointBExpr (BApp _ es _)) = CodePointOExpr (fst $ es !! i)
posMove (PosBLitEqL) (CodePointBExpr (BLitEq _ c _ _)) = CodePointCExpr c
posMove (PosBLitEqR) (CodePointBExpr (BLitEq _ _ e _)) = CodePointOExpr e
posMove (PosOGen) (CodePointOExpr (OGen s _)) = CodePointStmt s
posMove (PosOConst) (CodePointOExpr (OConst c _)) = CodePointCExpr c
posMove (PosOList i) (CodePointOExpr (OList es _)) = CodePointOExpr (es !! i)
posMove (PosORev) (CodePointOExpr (ORev e _)) = CodePointOExpr e
posMove (PosOIndexL) (CodePointOExpr (OIndex e _ _)) = CodePointOExpr e
posMove (PosOAppArg i) (CodePointOExpr (OApp _ es _)) = CodePointOExpr (fst $ es !! i)
posMove (PosCList i) (CodePointCExpr (CList es _)) = CodePointCExpr (es !! i)
posMove (PosFun f) (CodePointProg (Program fs _)) = CodePointFun $ fun
    where
        fun = head $ filter (\(StmtFun f' _ _ _) -> f == f') fs
posMove (PosFunBody) (CodePointFun (StmtFun _ _ s _)) = CodePointStmt s
posMove (PosFunArg i) (CodePointFun (StmtFun _ args _ _)) = CodePointVar $ (\(v, _, _) -> v) $ args !! i
posMove _ _ = error "Invalid move"


posMoveStar :: [PosMove] -> ProgramCodePoint t -> ProgramCodePoint t
posMoveStar [] p = p
posMoveStar (m:ms) p = posMoveStar ms $ posMove m p

posGoTo :: Pos -> ProgramCodePoint t -> ProgramCodePoint t
posGoTo (Pos ms) p = posMoveStar (reverse ms) p


data PosCoding = PosCoding (M.Map Pos Int) (IntMap.IntMap Pos)
    deriving (Show, Eq)

insertCoding :: Pos -> Int -> PosCoding -> PosCoding
insertCoding p i (PosCoding m1 m2) = PosCoding (M.insert p i m1) (IntMap.insert i p m2)

readPosCoding :: Pos -> PosCoding -> Int
readPosCoding p (PosCoding m _) = m M.! p

readIntCoding :: Int -> PosCoding -> Pos
readIntCoding i (PosCoding _ m) = m IntMap.! i


class (Monad m) => MonadPos m where
    withVar        :: String   -> m a -> m a
    withVars       :: [String] -> m a -> m a
    getVar         :: String -> m Int

    registerPos    :: [PosMove]  -> m Int

    readPosition   :: Pos  -> m Int
    readCodePoint  :: Int  -> m Pos

    logConstraint  :: C.GraphSpec -> m ()
    getConstraints :: m [C.GraphSpec]

    getPosRelation :: m PosCoding



data PosState = PosState {
    counter :: Int,
    coding  :: PosCoding,
    vars    :: M.Map String Int,
    constraints :: [C.GraphSpec]
} deriving (Eq,Show)

newtype PosStateM a = PosStateM { runPosStateM :: State PosState a }
    deriving (Functor, Applicative, Monad, MonadState PosState)


runPosState :: PosStateM a -> a
runPosState (PosStateM m) = evalState m $ PosState 0 (PosCoding M.empty IntMap.empty) M.empty []

instance MonadPos PosStateM where
    withVar v m = do
        counter <- gets counter
        oldVars <- gets vars
        let newCounter = counter + 1
        modify $ \s -> s { counter = newCounter, vars = M.insert v newCounter (vars s) }
        a <- m
        modify $ \s -> s { vars = oldVars }
        return a

    withVars vs m = do
        counter <- gets counter
        oldVars <- gets vars
        let newCounter = counter + length vs + 1
        modify $ \s -> s { counter = newCounter, vars = M.union (M.fromList $ zip vs [counter+1..]) (vars s) } 
        a <- m
        modify $ \s -> s { vars = oldVars }
        return a

    getVar v = do
        vars <- gets vars
        case M.lookup v vars of
            Just i -> return i
            Nothing -> error $ "(getVar) Variable " ++ v ++ " not found"

    registerPos p = do
        i <- gets counter
        let pos = Pos (reverse p)
        modify $ \s -> s { counter = i + 1, coding = insertCoding pos (i+1) (coding s) }
        return i

    readPosition p = do
        coding <- gets coding
        return $ readPosCoding p coding

    readCodePoint i = do
        coding <- gets coding
        return $ readIntCoding i coding

    logConstraint c = modify $ \s -> s { constraints = c : constraints s }
    getConstraints = gets constraints

    getPosRelation = gets coding

addTypeSpec :: (MonadPos m) => Int -> (Maybe ValueType) -> m ()
addTypeSpec i (Just t) = logConstraint $ C.VarType (i, valueTypeToCType t)
addTypeSpec _ _ = return ()

-- assignments provide the resulting number and the new statement
-- where the type is an actual variable.

assignNumbersStmtM :: (MonadPos m) => [PosMove] -> Stmt String (Maybe ValueType) -> m (Int, Stmt String Int)
assignNumbersStmtM p (SIf b s1 s2 t) = do
    n <- registerPos p
    addTypeSpec n t
    (nb, tb) <- assignNumbersBExprM (PosIfB : p) b
    addTypeSpec nb (Just TBool)
    (ns1, ts1) <- assignNumbersStmtM  (PosIfL : p) s1
    (ns2, ts2) <- assignNumbersStmtM  (PosIfR : p) s2
    logConstraint $ C.VarConstraint (ns1, C.Equal, n)
    logConstraint $ C.VarConstraint (ns2, C.Equal, n)
    return (n, SIf tb ts1 ts2 n)
assignNumbersStmtM p (SYield e t) = do
    n <- registerPos p
    addTypeSpec n t
    (ne, te) <- assignNumbersOExprM (PosYield : p) e
    logConstraint $ C.VarConstraint (ne, C.Minus, n)
    return (n, SYield te n)
assignNumbersStmtM p (SOReturn e t) = do
    n <- registerPos p
    addTypeSpec n t
    (ne, te) <- assignNumbersOExprM (PosORet : p) e
    logConstraint $ C.VarConstraint (ne, C.Equal, n)
    return (n, SOReturn te n)
assignNumbersStmtM p (SBReturn b t) = do
    n <- registerPos p
    addTypeSpec n t
    (nb, tb) <- assignNumbersBExprM (PosBRet : p) b
    logConstraint $ C.VarConstraint (nb, C.Equal, n)
    return (n, SBReturn tb n)
assignNumbersStmtM p (SLetOutput (v, tv) e s ts) = do
    n <- registerPos p
    addTypeSpec n ts
    withVar v $ do
        nv <- getVar v
        addTypeSpec nv tv
        (ne, te) <- assignNumbersOExprM (PosLetOVar : p) e
        logConstraint $ C.VarConstraint (nv, C.Minus, ne)
        (ns, ts) <- assignNumbersStmtM (PosLetOStmt : p) s
        logConstraint $ C.VarConstraint (ns, C.Equal, n)
        return (n, SLetOutput (v,nv) te ts n)
assignNumbersStmtM p (SLetBoolean v s t) = do
    n <- registerPos p
    addTypeSpec n t
    withVar v $ do
        nv <- getVar v
        addTypeSpec nv (Just TBool)
        (ns, ts) <- assignNumbersStmtM (PosLetBoolStmt : p) s
        logConstraint $ C.VarConstraint (ns, C.Equal, n)
        return (n, SLetBoolean v ts n)
assignNumbersStmtM p (SSetTrue v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    return (n, SSetTrue v n)
assignNumbersStmtM p (SFor (i, v, tv) e s ts) = do
    n <- registerPos p
    addTypeSpec n ts
    withVar v $ do
        nv <- getVar v
        addTypeSpec nv tv
        (ne, te) <- assignNumbersOExprM (PosForVar : p) e
        (ns, ts) <- assignNumbersStmtM  (PosForStmt : p) s
        logConstraint $ C.VarConstraint (nv, C.Minus, ne)
        logConstraint $ C.VarConstraint (ns, C.Equal, n)
        return (n, SFor (i, v, nv) te ts n)
assignNumbersStmtM p (SSeq [] t) = do
    n <- registerPos p
    addTypeSpec n t
    return (n, SSeq [] n)
assignNumbersStmtM p (SSeq ss t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- mapM (\(i,s) -> assignNumbersStmtM (PosSeq i : p) s) $ zip [0..] ss
    mapM_ (\(m1, m2) -> logConstraint $ C.VarConstraint (fst m1, C.Equal, fst m2)) $ zip ms (tail ms)
    logConstraint $ C.VarConstraint ((fst . head) ms, C.Equal, n)
    return (n, SSeq (map snd ms) n)

assignNumbersBExprM :: (MonadPos m) => [PosMove] -> BExpr String (Maybe ValueType) -> m (Int, BExpr String Int)
assignNumbersBExprM p (BConst b t) = do
    n <- registerPos p
    addTypeSpec n t
    addTypeSpec n (Just TBool)
    return (n, BConst b n)
assignNumbersBExprM p (BNot b t) = do
    n <- registerPos p
    addTypeSpec n t
    (nb, tb) <- assignNumbersBExprM (PosBNot : p) b
    logConstraint $ C.VarConstraint (nb, C.Equal, n)
    return (n, BNot tb n)
assignNumbersBExprM p (BOp op e1 e2 t) = do
    n <- registerPos p
    addTypeSpec n t
    (ne1, te1) <- assignNumbersBExprM (PosBOpL : p) e1
    (ne2, te2) <- assignNumbersBExprM (PosBOpR : p) e2
    logConstraint $ C.VarConstraint (ne1, C.Equal, n)
    logConstraint $ C.VarConstraint (ne2, C.Equal, n)
    return (n, BOp op te1 te2 n)
assignNumbersBExprM p (BComp op e1 e2 t) = do
    n <- registerPos p
    addTypeSpec n t
    let te1 = fmap (const (-1)) e1
    let te2 = fmap (const (-1)) e2
    return (n, BComp op te1 te2 n)
assignNumbersBExprM p (BVar v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    return (n, BVar v n)
assignNumbersBExprM p (BGen s t) = do
    n <- registerPos p
    addTypeSpec n t
    (ns, ts) <- assignNumbersStmtM (PosBGen : p) s
    logConstraint $ C.VarConstraint (ns, C.Equal, n)
    return (n, BGen ts n)
assignNumbersBExprM p (BApp v es t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- mapM (\(i, (e, _)) -> assignNumbersOExprM (PosBAppArg i : p) e) $ zip [0..] es
    argv <- forM [0..length ms] $ \i -> do
        readPosition . Pos $ [PosFun v, PosFunArg i]
    body <- readPosition . Pos $ [PosFun v, PosFunBody]
    mapM_ (\(m1, m2) -> logConstraint $ C.VarConstraint (fst m1, C.Equal, m2)) $ zip ms argv
    logConstraint $ C.VarConstraint (body, C.Equal, n)
    let newArgs = map (\((nmi, tmi),(_, pis)) -> (tmi, map (fmap (const (-1))) pis)) $ zip ms es
    return (n, BApp v newArgs n)
assignNumbersBExprM p (BLitEq t1 c e t2) = do
    n <- registerPos p
    addTypeSpec n t2
    (nc, tc) <- assignNumbersCExprM (PosBLitEqL : p) c
    (ne, te) <- assignNumbersOExprM (PosBLitEqR : p) e
    logConstraint $ C.VarConstraint (nc, C.Equal, ne)
    addTypeSpec ne t1
    addTypeSpec nc t1
    return (n, BLitEq nc tc te n)


assignNumbersOExprM :: (MonadPos m) => [PosMove] -> OExpr String (Maybe ValueType) -> m (Int, OExpr String Int)
assignNumbersOExprM p (OVar v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    return (n, OVar v n)
assignNumbersOExprM p (OConst c t) = do
    n <- registerPos p
    addTypeSpec n t
    (nc, tc) <- assignNumbersCExprM (PosOConst : p) c
    logConstraint $ C.VarConstraint (nc, C.Equal, n)
    return (n, OConst tc n)
assignNumbersOExprM p (OList [] t) = do
    n <- registerPos p
    addTypeSpec n t
    return (n, OList [] n)
assignNumbersOExprM p (OList es t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- mapM (\(i, e) -> assignNumbersOExprM (PosOList i : p) e) $ zip [0..] es
    mapM_ (\(m1, m2) -> logConstraint $ C.VarConstraint (fst m1, C.Equal, fst m2)) $ zip ms (tail ms)
    logConstraint $ C.VarConstraint (fst (head ms), C.Minus, n)
    return (n, OList (map snd ms) n)
assignNumbersOExprM p (ORev e t) = do
    n <- registerPos p
    addTypeSpec n t
    (ne, te) <- assignNumbersOExprM (PosORev : p) e
    logConstraint $ C.VarConstraint (ne, C.Equal, n)
    return (n, ORev te n)
assignNumbersOExprM p (OIndex e i t) = do
    n <- registerPos p
    addTypeSpec n t
    (ne, te) <- assignNumbersOExprM (PosOIndexL : p) e
    logConstraint $ C.VarConstraint (n, C.Minus, ne)
    let newPos = fmap (const (-1)) i
    return (n, OIndex te newPos n)
assignNumbersOExprM p (OApp f es t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- mapM (\(i, (e, _)) -> assignNumbersOExprM (PosOAppArg i : p) e) $ zip [0..] es
    -- for every argument, we search for the corresponding codepoint in the function
    -- [ PosFunArg i, PosFun f ] <-> Var i
    argv <- forM [0..length ms] $ \i -> do
        readPosition . Pos $ [PosFun f, PosFunArg i]
    body <- readPosition . Pos $ [PosFun f, PosFunBody]
    mapM_ (\(m1, m2) -> logConstraint $ C.VarConstraint (fst m1, C.Equal, m2)) $ zip ms argv
    logConstraint $ C.VarConstraint (body, C.Equal, n)
    let newArgs = map (\((nmi, tmi),(_, pis)) -> (tmi, map (fmap (const (-1))) pis)) $ zip ms es
    return (n, OApp f newArgs n)
assignNumbersOExprM p (OGen s t) = do
    n <- registerPos p
    addTypeSpec n t
    (ns, ts) <- assignNumbersStmtM (PosOGen : p) s
    logConstraint $ C.VarConstraint (ns, C.Equal, n)
    return (n, OGen ts n)

assignNumbersCExprM :: (MonadPos m) => [PosMove] -> CExpr String (Maybe ValueType) -> m (Int, CExpr String Int)
assignNumbersCExprM p (CChar c t) = do
    n <- registerPos p
    addTypeSpec n t
    return (n, CChar c n)
assignNumbersCExprM p (CList [] t) = do
    n <- registerPos p
    addTypeSpec n t
    return (n, CList [] n)
assignNumbersCExprM p (CList es t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- mapM (\(i, e) -> assignNumbersCExprM (PosCList i : p) e) $ zip [0..] es
    mapM_ (\(m1, m2) -> logConstraint $ C.VarConstraint (fst m1, C.Equal, fst m2)) $ zip ms (tail ms)
    logConstraint $ C.VarConstraint (fst (head ms), C.Minus, n)
    return (n, CList (map snd ms) n)


assignNumbersProgramM :: (MonadPos m) => Program String (Maybe ValueType) -> m (Program String Int)
assignNumbersProgramM (Program funcs main) = do 
    newFuncs <- assignNumbersFuncsM funcs
    return $ Program newFuncs main

assignNumbersFuncsM :: (MonadPos m) => [StmtFun String (Maybe ValueType)] -> m [StmtFun String Int]
assignNumbersFuncsM [] = return []
assignNumbersFuncsM (StmtFun f args s t : fs) = do
    -- assign a number to the arguments
    iargs <- mapM (\(i,_) -> registerPos [PosFunArg i, PosFun f]) $ zip [0..] args
    -- add constraints for the arguments
    mapM_ (\(i, (_, t, _)) -> addTypeSpec i t) $ zip iargs args
    -- assign body things
    (nbody, tbody) <- (withVars (map (\(v,_,_) -> v) args) $ do
        forM_ (zip args iargs) ( \((v,_,_), i) -> do
            nv <- getVar v
            logConstraint $ C.VarConstraint (nv, C.Equal, i))
        assignNumbersStmtM [PosFunBody, PosFun f] s)
    addTypeSpec nbody t
    -- continue with the rest of the functions
    newfs <- assignNumbersFuncsM fs
    let newArgs = map (\((v,_,ps),t) -> (v, t, ps)) $ zip args iargs
    return $ StmtFun f newArgs tbody nbody : newfs

computeNumbersAndConstraints :: (MonadPos m) => Program String (Maybe ValueType) -> m (Program String Int, PosCoding, C.ConstraintGraph)
computeNumbersAndConstraints p = do
    newP <- assignNumbersProgramM p
    coding      <- getPosRelation
    constraints <- getConstraints
    let cgraph = C.createGraph constraints
    return (newP, coding, cgraph)

data InferError = InferError String
  deriving (Show)


resolveType :: IntMap.IntMap C.Type -> Int -> Maybe ValueType
resolveType m i = case IntMap.lookup i m of
    Just t -> Just $ cTypeToValueType t
    Nothing -> Nothing

inferTypes :: Program String (Maybe ValueType) -> Either (InferError) (Program String (Maybe ValueType))
inferTypes p = runInfer p
    where
        runInfer p = do
            let (prog, _, cgraph) = runPosState $ computeNumbersAndConstraints p
            case C.solveConstraints cgraph of
                Left e -> Left $ InferError (show e)
                Right intToType -> Right $ fmap (resolveType intToType) prog
