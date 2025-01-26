{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.HighLevel.Typing.Inference (inferAndCheckProgram)
where

import qualified Data.Map.Strict as M
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

import qualified ForPrograms.HighLevel.Typing.Constraints as C
import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing(ValueType(..), 
                          OutputType(..), 
                          Position(..), 
                          eraseTypesO,
                          outputTypeDepth,
                          depthToType)
import Logic.QuantifierFree
import ForPrograms.HighLevel.PrettyPrint

import Control.Monad
import Control.Monad.State

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
             | PosForIndex
             | PosForExpr 
             | PosForStmt 
             | PosSeq Int 
             | PosBNot 
             | PosBOpL | PosBOpR 
             | PosBGen 
             | PosBCompL
             | PosBCompR
             | PosBLitEqL 
             | PosBLitEqR 
             | PosOGen 
             | PosOConst 
             | PosOList Int
             | PosOExprRoot
             | PosCList Int
             | PosAppArg Int
             | PosAppArgPos Int Int
             | PosFun String
             | PosFunBody 
             | PosFunArg  Int
             | PosFunArgPos Int Int
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

prettyPrintCodePoint :: (Show t) => ProgramCodePoint t -> String
prettyPrintCodePoint (CodePointStmt s) = "CodePointStmt " ++ prettyPrintStmtWithNlsNoTypes 0 s
prettyPrintCodePoint (CodePointBExpr b) = "CodePointBExpr " ++ prettyPrintBExprWithNlsNoTypes 0 0 b
prettyPrintCodePoint (CodePointOExpr e) = "CodePointOExpr " ++ prettyPrintOExprWithNlsNoTypes 0 e
prettyPrintCodePoint (CodePointCExpr c) = "CodePointCExpr " ++ prettyPrintCExprWithNlsNoTypes c
prettyPrintCodePoint (CodePointFun f) = "CodePointFun " ++ prettyPrintFunctionWithNlsNoTypes f
prettyPrintCodePoint (CodePointProg p) = "CodePointProg " ++ prettyPrintProgramWithNoTypes p
prettyPrintCodePoint (CodePointVar v) = "CodePointVar " ++ v




cTypeToValueType :: C.Type -> ValueType
cTypeToValueType C.TBool = TBool
cTypeToValueType (C.TList n) = TOutput . depthToType $ n
cTypeToValueType (C.TPos t) = TPos $ Position t

valueTypeToCType :: ValueType -> C.Type
valueTypeToCType TBool = C.TBool
valueTypeToCType (TOutput t) = C.TList $ outputTypeDepth t
valueTypeToCType (TPos (Position t)) = C.TPos t



posMove :: (Show t) => PosMove -> ProgramCodePoint t -> ProgramCodePoint t
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
posMove (PosForVar) (CodePointStmt (SFor _ (_,v, _) _ _ _)) = CodePointVar v
posMove (PosForIndex) (CodePointStmt (SFor _ (v, _, _) _ _ _)) = CodePointVar v
posMove (PosForExpr) (CodePointStmt (SFor _ _ e _ _)) = CodePointOExpr e
posMove (PosForStmt) (CodePointStmt (SFor _ _ _ s _)) = CodePointStmt s
posMove (PosSeq i) (CodePointStmt (SSeq ss _)) = CodePointStmt (ss !! i)
posMove (PosBNot) (CodePointBExpr (BNot b _)) = CodePointBExpr b
posMove (PosBOpL) (CodePointBExpr (BOp _ e _ _)) = CodePointBExpr e
posMove (PosBOpR) (CodePointBExpr (BOp _ _ e _)) = CodePointBExpr e
posMove (PosBGen) (CodePointBExpr (BGen s _)) = CodePointStmt s
posMove (PosBLitEqL) (CodePointBExpr (BLitEq _ c _ _)) = CodePointCExpr c
posMove (PosBLitEqR) (CodePointBExpr (BLitEq _ _ e _)) = CodePointOExpr e
posMove (PosOGen) (CodePointOExpr (OGen s _)) = CodePointStmt s
posMove (PosOConst) (CodePointOExpr (OConst c _)) = CodePointCExpr c
posMove (PosOList i) (CodePointOExpr (OList es _)) = CodePointOExpr (es !! i)
posMove (PosCList i) (CodePointCExpr (CList es _)) = CodePointCExpr (es !! i)
posMove (PosFun f) (CodePointProg (Program fs _)) = CodePointFun $ fun
    where
        fun = head $ filter (\(StmtFun f' _ _ _) -> f == f') fs
posMove (PosFunBody) (CodePointFun (StmtFun _ _ s _)) = CodePointStmt s
posMove (PosFunArg i) (CodePointFun (StmtFun _ args _ _)) = CodePointVar $ (\(v, _, _) -> v) $ args !! i
posMove x _ = error $ "Invalid move" ++ show x


posMoveStar :: (Show t) => [PosMove] -> ProgramCodePoint t -> ProgramCodePoint t
posMoveStar [] p = p
posMoveStar (m:ms) p = posMoveStar ms $ posMove m p

posGoTo :: (Show t) => Pos -> ProgramCodePoint t -> ProgramCodePoint t
posGoTo (Pos ms) p = posMoveStar ( ms) p


data PosCoding = PosCoding (M.Map Pos Int) (IntMap.IntMap Pos)
    deriving (Show, Eq)

insertCoding :: Pos -> Int -> PosCoding -> PosCoding
insertCoding p i (PosCoding m1 m2) = PosCoding (M.insert p i m1) (IntMap.insert i p m2)

insertCodings :: [(Pos, Int)] -> PosCoding -> PosCoding
insertCodings ps (PosCoding m1 m2) = PosCoding (M.union newMap m1) (IntMap.union newMap' m2)
    where
        newMap  = M.fromList ps
        newMap' = IntMap.fromList $ map (\(p, i) -> (i, p)) ps

readPosCoding :: PosCoding -> Pos -> Int
readPosCoding (PosCoding m _) p = m M.! p

readIntCoding :: PosCoding -> Int -> Pos
readIntCoding (PosCoding _ m) i = m IntMap.! i


class (Monad m) => MonadPos m where
    withVar        :: String -> [PosMove] -> m a -> m a
    withVars       :: [(String, [PosMove])] -> m a -> m a
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
runPosState (PosStateM m) = evalState m $ PosState (-1) (PosCoding M.empty IntMap.empty) M.empty []

instance MonadPos PosStateM where
    withVar v p m = do
        counter <- gets counter
        oldVars <- gets vars
        let newCounter = counter + 1
        let pos = Pos (reverse p)
        modify $ \s -> s { counter = newCounter,
                           vars = M.insert v newCounter (vars s), 
                           coding = insertCoding pos newCounter (coding s) }
        a <- m
        modify $ \s -> s { vars = oldVars }
        return a

    withVars vps m = do
        counter <- gets counter
        oldVars <- gets vars
        let newCounter = counter + length vps
        let poss = map (Pos . reverse . snd) vps
        modify $ \s -> s { counter = newCounter, 
                           vars = M.union (M.fromList $ zip (map fst vps) [counter+1..]) (vars s),
                           coding = insertCodings (zip poss [counter+1..]) (coding s) }
        a <- m
        modify $ \s -> s { vars = oldVars }
        return a

    getVar v = do
        vars <- gets vars
        case M.lookup v vars of
            Just i -> return i
            Nothing -> error $ "(getVar) Variable " ++ v ++ " not found in " ++ show vars

    registerPos p = do
        i <- gets counter
        --let pos = Pos p
        let pos = Pos (reverse p)
        PosCoding c _ <- gets coding 
        modify $ \s -> s { counter = i + 1, coding = insertCoding pos (i+1) (coding s) }
        return (i+1)

    readPosition p = do
        coding <- gets coding
        return $ readPosCoding coding p

    readCodePoint i = do
        coding <- gets coding
        return $ readIntCoding coding i

    logConstraint c = do 
        modify $ \s -> s { constraints = c : constraints s }

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
assignNumbersStmtM p (SLetOutput (v, t1) e s t2) = do
    n <- registerPos p
    addTypeSpec n t2
    withVar v (PosLetOVar : p) $ do
        nv <- getVar v
        addTypeSpec nv t1
        (ne, te) <- assignNumbersOExprM (PosLetOExpr : p) e
        logConstraint $ C.VarConstraint (nv, C.Equal, ne)
        (ns, ts) <- assignNumbersStmtM (PosLetOStmt : p) s
        logConstraint $ C.VarConstraint (ns, C.Equal, n)
        return (n, SLetOutput (v,nv) te ts n)
assignNumbersStmtM p (SLetBoolean v s t) = do
    n <- registerPos p
    addTypeSpec n t
    withVar v (PosLetBoolVar : p) $ do
        nv <- getVar v
        addTypeSpec nv (Just TBool)
        (ns, ts) <- assignNumbersStmtM (PosLetBoolStmt : p) s
        logConstraint $ C.VarConstraint (ns, C.Equal, n)
        return (n, SLetBoolean v ts n)
assignNumbersStmtM p (SSetTrue v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    addTypeSpec nv (Just TBool)
    return (n, SSetTrue v n)
assignNumbersStmtM p (SFor dir (i, v, tv) e s ts) = do
    n <- registerPos p
    addTypeSpec n ts
    withVar v (PosForVar : p) $ do
        withVar i (PosForIndex : p) $ do 
            nv <- getVar v
            ni <- getVar i
            addTypeSpec nv tv
            addTypeSpec ni $ Just (TPos (Position (eraseTypesO e)))
            (ne, te) <- assignNumbersOExprM (PosForExpr  : p) e
            (ns, ts) <- assignNumbersStmtM  (PosForStmt : p) s
            logConstraint $ C.VarConstraint (nv, C.Minus, ne)
            logConstraint $ C.VarConstraint (ns, C.Equal, n)
            return (n, SFor dir (i, v, nv) te ts n)
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
    addTypeSpec n (Just TBool)
    addTypeSpec n t
    (nb, tb) <- assignNumbersBExprM (PosBNot : p) b
    logConstraint $ C.VarConstraint (nb, C.Equal, n)
    return (n, BNot tb n)
assignNumbersBExprM p (BOp op e1 e2 t) = do
    n <- registerPos p
    addTypeSpec n (Just TBool)
    addTypeSpec n t
    (ne1, te1) <- assignNumbersBExprM (PosBOpL : p) e1
    (ne2, te2) <- assignNumbersBExprM (PosBOpR : p) e2
    logConstraint $ C.VarConstraint (ne1, C.Equal, n)
    logConstraint $ C.VarConstraint (ne2, C.Equal, n)
    return (n, BOp op te1 te2 n)
assignNumbersBExprM p (BComp op e1 e2 t) = do
    n <- registerPos p
    addTypeSpec n t
    addTypeSpec n (Just TBool)
    (ne1, te1) <- assignNumbersPExprM (PosBCompL : p) e1
    (ne2, te2) <- assignNumbersPExprM (PosBCompR : p) e2
    logConstraint $ C.VarConstraint (ne1, C.Equal, ne2)
    return (n, BComp op te1 te2 n)
assignNumbersBExprM p (BVar v t) = do
    n <- registerPos p
    addTypeSpec n (Just TBool)
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    return (n, BVar v n)
assignNumbersBExprM p (BGen s t) = do
    n <- registerPos p
    addTypeSpec n (Just TBool)
    addTypeSpec n t
    (ns, ts) <- assignNumbersStmtM (PosBGen : p) s
    logConstraint $ C.VarConstraint (ns, C.Equal, n)
    return (n, BGen ts n)
assignNumbersBExprM p (BApp v es t) = do
    n <- registerPos p
    addTypeSpec n (Just TBool)
    addTypeSpec n t
    ms <- assignAppArgsPositionsM p es
    argv <- forM [0..length ms] $ \i -> do
        readPosition . Pos $ [PosFun v, PosFunArg i]
    body <- readPosition . Pos $ [PosFun v, PosFunBody]
    mapM_ (\((nm1,_,_), m2) -> logConstraint $ C.VarConstraint (nm1, C.Equal, m2)) $ zip ms argv
    logConstraint $ C.VarConstraint (body, C.Equal, n)
    let newArgs = map (\(_, a,b) -> (a,b)) ms
    return (n, BApp v newArgs n)
assignNumbersBExprM p (BLitEq t1 c e t2) = do
    n <- registerPos p
    addTypeSpec n t2
    addTypeSpec n (Just TBool)
    (nc, tc) <- assignNumbersCExprM (PosBLitEqL : p) c
    (ne, te) <- assignNumbersOExprM (PosBLitEqR : p) e
    logConstraint $ C.VarConstraint (nc, C.Equal, ne)
    addTypeSpec ne t1
    addTypeSpec nc t1
    return (n, BLitEq nc tc te n)

assignAppArgsPositionsM :: (MonadPos m) =>
                           [PosMove] -> 
                           [(OExpr String (Maybe ValueType), [PExpr String (Maybe ValueType)])] 
                           -> m [(Int, OExpr String Int, [PExpr String Int])]
assignAppArgsPositionsM p es = do
    forM (zip [0..] es) $ \(i, (e, ps)) -> do
        (ne, te) <- assignNumbersOExprM (PosAppArg i : p) e
        newpos   <- forM (zip [0..] ps) $ \(j, position) -> do
            (np, tp) <- assignNumbersPExprM (PosAppArgPos i j : p) position
            addTypeSpec np (Just . TPos $ Position (eraseTypesO e))
            return tp
        return (ne, te, newpos)

assignNumbersPExprM :: (MonadPos m) => [PosMove] -> PExpr String (Maybe ValueType) -> m (Int, PExpr String Int)
assignNumbersPExprM p (PVar v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    return (n, PVar v n)

assignNumbersOExprM :: (MonadPos m) => [PosMove] -> OExpr String (Maybe ValueType) -> m (Int, OExpr String Int)
assignNumbersOExprM p (OVar v t) = do
    n <- registerPos p
    addTypeSpec n t
    nv <- getVar v
    logConstraint $ C.VarConstraint (nv, C.Equal, n)
    constraints <- getConstraints
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
assignNumbersOExprM p (OApp f es t) = do
    n <- registerPos p
    addTypeSpec n t
    ms <- assignAppArgsPositionsM p es
    -- for every argument, we search for the corresponding codepoint in the function
    -- [ PosFunArg i, PosFun f ] <-> Var i
    argv <- forM [0..length ms] $ \i -> do
        readPosition . Pos $ [PosFun f, PosFunArg i]
    body <- readPosition . Pos $ [PosFun f, PosFunBody]
    mapM_ (\((m1,_,_), m2) -> logConstraint $ C.VarConstraint (m1, C.Equal, m2)) $ zip ms argv
    logConstraint $ C.VarConstraint (body, C.Equal, n)
    let newArgs = map (\(a,b,c) -> (b,c)) ms
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
    -- argument positions
    let pargs = map (\i -> [PosFunArg i , PosFun f]) [0..] 
    -- argument names
    let nargs = map (\(v,_,_) -> v) args
    -- argument position names
    let pargsP = do
                        (i, (v, t, ps)) <- zip [0..] args
                        (j, p) <- zip [0..] ps
                        return (p, [PosFunArgPos i j, PosFun f])
    -- assign body things 
    (iargs, nbody, tbody) <- withVars (zip nargs pargs) $ withVars pargsP $ do
        -- first we collect potential type constraints
        -- on the function’s arguments
        iargs <- forM args $ \(v, t, ps) -> do
            nv <- getVar v
            addTypeSpec nv t
            forM_ ps $ \p -> do
                np <- getVar p
                addTypeSpec np (Just . TPos $ Position (OVar v ()))
            return nv
        -- then we assign numbers to the body
        (nbody, tbody) <- assignNumbersStmtM [PosFunBody, PosFun f] s
        return (iargs, nbody, tbody)
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

instance (Show InferError) where
    show (InferError s) = "InferError:\n" ++ s


resolveType :: IntMap.IntMap C.Type -> Int -> Maybe ValueType
resolveType m i = case IntMap.lookup i m of
    Just t -> Just $ cTypeToValueType t
    Nothing -> Nothing

displayUncoveredSingleNode:: PosCoding -> Int -> String
displayUncoveredSingleNode (PosCoding _ b) i = case IntMap.lookup i b of
    Just p  -> "Node " ++ show i ++ " at " ++ show p
    Nothing -> "Node " ++ show i ++ " not found"

displayUncoveredNodesBag :: PosCoding -> IntSet.IntSet -> String
displayUncoveredNodesBag coding ns = unlines . map (displayUncoveredSingleNode coding ) $ l
    where
        l = IntSet.toList ns

displayUncoveredNodes :: PosCoding -> [IntSet.IntSet] -> String
displayUncoveredNodes (PosCoding _ b) ns = show (IntMap.keys b)  ++ " ; " ++ unlines (map (displayUncoveredNodesBag (PosCoding M.empty b)) ns)


displayNodeOrType :: Program String (Maybe ValueType) -> PosCoding -> C.ConstraintGraph -> Int -> String
displayNodeOrType p (PosCoding _ b) cgraph  i = case IntMap.lookup i b of
    Just pos  -> "Node " ++ show i ++ " at " ++ show pos ++ "\n" ++ prettyPrintCodePoint (posGoTo pos (CodePointProg p))
    Nothing -> case IntMap.lookup i (C.csts cgraph) of
        Just t  -> "Constant Type " ++ show i ++ " : " ++ show t
        Nothing -> error "Node not found"


resolveTypeOrError :: IntMap.IntMap C.Type -> Int -> Either InferError ValueType
resolveTypeOrError m i = case IntMap.lookup i m of
    Just t ->  Right $ cTypeToValueType t
    Nothing -> Left $ InferError $ "Type not found for node " ++ show i

displaySolverError :: Program String (Maybe ValueType) -> PosCoding -> C.ConstraintGraph -> C.SolverError -> String
displaySolverError p coding cgraph (C.UncoveredNodes ns) = "Uncovered nodes: " ++ show (C.csts cgraph) ++ displayUncoveredNodes coding ns 
displaySolverError p coding cgraph (C.InvalidConstraint x y c t) = "Invalid constraint: " ++ show x ++ ":" ++ show (readIntCoding coding x) ++ " " ++ show y ++ ":" ++ show (readIntCoding coding y) ++ " " ++ show c ++ " " ++ show t 
displaySolverError p coding cgraph (C.InconsistentGraph x y c tx ty) = "Inconsistent graph: " ++ (displayNodeOrType p coding cgraph x) ++ " " ++ (displayNodeOrType p coding cgraph y) ++ " " ++ show c ++ " " ++ show tx ++ " " ++ show ty 

inferAndCheckProgram :: Program String (Maybe ValueType) -> Either (InferError) (Program String ValueType)
inferAndCheckProgram p = runInfer p
    where
        runInfer p = do
            let (prog, coding, cgraph) = runPosState $ computeNumbersAndConstraints p
            case C.verifyAndSolveBFS cgraph of
                Left errs -> Left $ InferError $ unlines $ (map $ displaySolverError p coding cgraph) $ take 23 errs
                Right intToType -> mapM (resolveTypeOrError intToType) prog
