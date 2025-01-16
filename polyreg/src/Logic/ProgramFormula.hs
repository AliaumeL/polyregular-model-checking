{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Logic.ProgramFormula where

import qualified SimpleForPrograms as SFP
import SimpleForPrograms (Direction(..), BName(..), PName(..), Movement(..))

import Data.Map (Map)
import qualified Data.Map as M

import Logic.Formulas
import QuantifierFree

import Debug.Trace

-- | A formula seen as a morphism in the category of something
-- so that they can be composed.
data ProgramFormula tag  = ProgramFormula {
    -- | the formula recognizing the function
    formula    :: Formula tag ,
    -- | the input variables (with their sorts)
    inputVars  :: Map String Sort,
    -- | the output variables (with their sorts)
    outputVars :: Map String Sort
} deriving (Eq) 

printProgramFormulaGeneric :: ProgramFormula tag  -> String
printProgramFormulaGeneric (ProgramFormula φ iφ oφ) = unlines $ 
    ["INPUT: " ++ show iφ, "OUTPUT: " ++ show oφ, "FORMULA: " ++ showFormulaGeneric φ]

typeCheckProgramFormula :: ProgramFormula tag  -> Bool
typeCheckProgramFormula (ProgramFormula φ iφ oφ) = 
    let (iφ', oφ') = freeVars φ in
    iφ == iφ' && oφ == oφ'

forceTypeCheck :: ProgramFormula tag  -> ProgramFormula tag
forceTypeCheck (ProgramFormula φ iφ oφ) = ProgramFormula φ iφ' oφ'
    where
        (iφ', oφ') = freeVars φ

typeCheckOrFail :: ProgramFormula tag  -> a -> a
typeCheckOrFail φ x = if typeCheckProgramFormula φ then x else error $ unlines $
    [ "typeCheckOrFail: type error",
      (printProgramFormulaGeneric φ),
      "FreeVars: " ++ show (freeVars $ formula φ) ]


instance Show tag => Show (ProgramFormula tag ) where
    show (ProgramFormula φ iφ oφ) = unlines [
        "ProgramFormula",
        "\tFormula",
        show φ,
        "\tInputVars",
        show iφ,
        "\tOutputVars",
        show oφ
        ]

data ProgramFormulaValuation = ProgramFormulaValuation {
    valAllTags   :: [String],
    valInputWord :: String,     
    valPositions :: Map Var Int,
    valBooleans  :: Map Var Bool,
    valTags      :: Map Var String
} deriving (Eq,Show)

evalProgramFormula :: ProgramFormulaValuation -> ProgramFormula String -> Bool
evalProgramFormula (ProgramFormulaValuation allTags w pos bools tgs) (ProgramFormula φ iφ oφ) = evalFormulaWithFreeVars φ' allVals allTags w
    where
        φ' = mapOutVars (\_ x -> In ("out_" ++ x)) . mapInVars (\_ x -> In ("in_" ++ x)) $ φ
        allVals = allPosVals ++ allBoolVals ++ allTagVals

        allPosVals :: [(String, Value)]
        allPosVals = do 
            (x, i) <- M.toList pos
            case x of 
                In x      -> return ("in_" ++ x, PosVal i)
                Out x     -> return ("out_" ++ x, PosVal i)
                _         -> error "evalProgramFormula: local position variable"

        allBoolVals :: [(String, Value)]
        allBoolVals = do 
            (x, b) <- M.toList bools
            case x of 
                In x      -> return ("in_" ++ x, BoolVal b)
                Out x     -> return ("out_" ++ x, BoolVal b)
                _         -> error "evalProgramFormula: local boolean variable"

        allTagVals :: [(String, Value)]
        allTagVals = do 
            (x, t) <- M.toList tgs
            case x of 
                In x      -> return ("in_" ++ x, TagVal t)
                Out x     -> return ("out_" ++ x, TagVal t)
                _         -> error "evalProgramFormula: local tag variable"





ignoreOutputVarUnsafe :: String -> ProgramFormula tag  -> ProgramFormula tag 
ignoreOutputVarUnsafe x (ProgramFormula φ iφ oφ) = ProgramFormula φ' iφ' oφ'
    where
        s   = oφ M.! x
        φ'  = FQuant Exists x s $ quantOutVars f φ
        iφ' = iφ
        oφ' = M.delete x oφ
        f y = if x == y then Just (0, y) else Nothing

ignoreOutputVar :: String -> ProgramFormula tag  -> ProgramFormula tag
ignoreOutputVar x p@(ProgramFormula _ _ oφ) =  case M.lookup x oφ of
                                                    Just _  -> ignoreOutputVarUnsafe x p
                                                    Nothing -> typeCheckOrFail p p

ignoreOutputVars :: [String] -> ProgramFormula tag  -> ProgramFormula tag 
ignoreOutputVars xs φ = foldr ignoreOutputVar φ xs


withFalseInput :: String -> ProgramFormula tag  -> ProgramFormula tag 
withFalseInput x p@(ProgramFormula φ iφ oφ) = typeCheckOrFail p $ ProgramFormula φ' iφ' oφ
    where
        φ'  = substituteBooleanVar f φ
        f y = if y == In x then FConst False else FVar y
        iφ' = M.delete x iφ

withFalseInputs :: [String] -> ProgramFormula tag  -> ProgramFormula tag
withFalseInputs xs φ = foldr withFalseInput φ xs


instance Semigroup (ProgramFormula tag ) where
    (ProgramFormula φ iφ oφ) <> (ProgramFormula ψ iψ oψ) = ProgramFormula θ iθ oθ
        where
            commonVars :: Map String Sort
            commonVars = M.intersection oφ iψ

            commonVarsSorted :: [(String, Sort, Quant)]
            commonVarsSorted = do 
                (x, s) <- M.toList commonVars
                return (x, s, Exists)

            commonVarsQ :: Map String Int
            commonVarsQ = M.fromList $ zip (map (\(x,_,_) -> x) commonVarsSorted) [0..]

            erasedVars :: Map String Sort
            erasedVars = (oψ `M.intersection` oφ) `M.difference` iψ

            iθ :: Map String Sort
            iθ = iφ `M.union` (iψ `M.difference` commonVars)

            oθ :: Map String Sort
            oθ = oψ `M.union` (oφ `M.difference` commonVars)

            (ProgramFormula φ' _ _) = ignoreOutputVars (M.keys erasedVars)
                                                       (ProgramFormula φ iφ oφ)

            ψ' = ψ

            fφ :: String -> Maybe (Int, String)
            fφ x = case M.lookup x commonVarsQ of
                        Just i   -> Just (i, x)
                        Nothing  -> Nothing

            fψ :: String -> Maybe (Int, String)
            fψ = fφ

            φ'' = quantOutVars fφ φ'

            ψ'' = quantInVars  fψ ψ'

            θ = quantifyList commonVarsSorted $ andList [φ'', ψ'']

instance Monoid (ProgramFormula tag ) where
    mempty = ProgramFormula (FConst True) M.empty M.empty


withNewBoolVar :: String -> ProgramFormula tag  -> ProgramFormula tag 
withNewBoolVar x p = ignoreOutputVar x $ withFalseInput x $ typeCheckOrFail p p

withNewBoolVars :: [String] -> ProgramFormula tag  -> ProgramFormula tag 
withNewBoolVars xs p = foldr withNewBoolVar p xs



setTrueBoolean :: String -> ProgramFormula tag 
setTrueBoolean x = ProgramFormula φ iφ oφ
    where
        φ  = FBin Equiv (FVar $ Out x) (FConst True)
        iφ = M.empty
        oφ = M.singleton x Boolean



boolExprToFormula :: SFP.BoolExpr -> Formula tag 
boolExprToFormula (SFP.BVar (BName v)) = FVar $ In v
boolExprToFormula (SFP.BConst b) = FConst b
boolExprToFormula (SFP.BNot e) = FNot $ boolExprToFormula e
boolExprToFormula (SFP.BBin op l r) = FBin op (boolExprToFormula l) (boolExprToFormula r)
boolExprToFormula (SFP.BTest op (PName x) (PName y)) = FTestPos op (In x) (In y)
boolExprToFormula (SFP.BLabelAt (PName x) t) = FLetter (In x) t


ifThenElse :: SFP.BoolExpr -> ProgramFormula tag  -> ProgramFormula tag  -> ProgramFormula tag 
ifThenElse b (ProgramFormula φ iφ oφ) (ProgramFormula ψ iψ oψ) = ProgramFormula ξ iξ oξ
    where
        θ = boolExprToFormula b

        totalOutputVars :: Map String Sort
        totalOutputVars = oφ `M.union` oψ

        missingOutputφ :: Map String Sort
        missingOutputφ = totalOutputVars `M.difference` oφ

        missingOutputψ :: Map String Sort
        missingOutputψ = totalOutputVars `M.difference` oψ

        identityMissingOutputφ :: Formula tag 
        identityMissingOutputφ = andList $ do 
            (x, s) <- M.toList missingOutputφ
            case s of 
                Boolean -> return $ FBin Equiv (FVar $ Out x) (FVar $ In x)
                _       -> error $ "ifThenElse: output variable " ++ x ++ " is not a boolean"

        identityMissingOutputψ :: Formula tag 
        identityMissingOutputψ = andList $ do 
            (x, s) <- M.toList missingOutputψ
            case s of 
                Boolean -> return $ FBin Equiv (FVar $ Out x) (FVar $ In x)
                _       -> error $ "ifThenElse: output variable " ++ x ++ " is not a boolean"
        
        ξ = orList [
                     andList [φ, identityMissingOutputφ, θ],
                     andList [ψ, identityMissingOutputψ, FNot θ ]
                   ]

        (iθ, _) = freeVars θ

        iξ = iφ `M.union` iψ `M.union` iθ

        oξ = totalOutputVars




iterOverVar :: Direction -> String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVar dir p (ProgramFormula φ iφ oφ) =  ProgramFormula ξ iξ oξ
    where
        -- the number of output variables of φ, i.e., the ones
        -- that can actually *change* by computing φ
        unum :: Int
        unum = M.size oφ

        -- for every number 1 <= i <= unum
        -- we create a Position variable p_i
        iterPosVars :: [(Int, String, Sort)]
        iterPosVars = do
            i <- [1 .. unum]
            return (i, "p_" ++ show i, Pos)

        -- and variables "x_i" for all output variables x of φ
        iterUpdtVars :: [(Int, String, Sort)]
        iterUpdtVars = do
            i <- [1 .. (unum-1)]
            (x, s) <- M.toList oφ
            return (i, x, s)

        -- all quantified vars
        allVars :: [(Int, String, Sort)]
        allVars = iterUpdtVars ++ iterPosVars

        -- allVars as a map from (i, s) to the number of the quantified variable
        updtVarMap :: Map (Int, String) Int
        updtVarMap = M.fromList $ zip (map (\(i, x, _) -> (i, x)) iterUpdtVars) [0..]

        posVarMap  :: Map Int Int
        posVarMap  = M.fromList $ zip (map (\(i, _, _) -> i) iterPosVars) [length iterUpdtVars ..]

        -- finds the corresponding boolean variable
        -- for the variable x at iteration i
        getUpdtVar :: Int -> Int -> String -> Var 
        getUpdtVar 0    depth x = In x
        getUpdtVar n    depth x | n == unum = Out x
        getUpdtVar step depth x = case M.lookup (step, x) updtVarMap of
                                    Just i  -> Local (depth + i) x
                                    Nothing -> error $ "iterUntil: boolean variable " ++ x ++ " not found"

        getPosVar :: Int -> Int -> String -> Var 
        getPosVar step depth x | x == p = case M.lookup step posVarMap of
                                            Just i  -> Local (depth + i) x
                                            Nothing -> error $ "iterUntil: position variable " ++ x ++ " not found"
        getPosVar step depth x = In x

        -- Now, we construct the formulas [φ_i] for 0 <= i <= unum - 1
        -- where φ_i is φ with input   variables (updtVarMap i)
        -- and                 output  variables (updtVarMap i+1)
        subφ i = mapInVars (getUpdtVar i) $ 
                    mapOutVars (getUpdtVar (i+1)) $ 
                        mapInVars (getPosVar (i+1)) φ

        correctφ = andList $ [ subφ i | i <- [0 .. unum - 1] ]

        -- condIntermediate => pi < p < p{i+1} 
        -- or                     >   >
        -- with p0 = 0 and pn = infty
        condIntermediate LeftToRight 0 x | 0 == unum = FConst True
        condIntermediate RightToLeft 0 x | 0 == unum = FConst True
        condIntermediate LeftToRight 0 x = 
            FTestPos Lt x (Local (1 + (posVarMap M.! 1)) p)
        condIntermediate RightToLeft 0 x = 
            FTestPos Gt x (Local (1 + (posVarMap M.! 1)) p)
        condIntermediate LeftToRight i x | i == unum =
            FTestPos Gt x (Local (1 + (posVarMap M.! unum)) p)
        condIntermediate RightToLeft i x | i == unum =
            FTestPos Lt x (Local (1 + (posVarMap M.! unum)) p)
        condIntermediate LeftToRight i x = andList [
            FTestPos Lt x (Local (1 + (posVarMap M.! i)) p),
            FTestPos Gt x (Local (1 + (posVarMap M.! (i+1))) p)
            ]
        condIntermediate RightToLeft i x = andList [
            FTestPos Gt x (Local (1 + (posVarMap M.! i)) p),
            FTestPos Lt x (Local (1 + (posVarMap M.! (i+1))) p)
            ]
        

        quantifyIntermediatePos i λ = quantifyList [("pj", Pos, Forall)] $
                mapInVars (\d x -> if x == p then Local d "pj" else In x) $ 
                    FBin Impl (condIntermediate dir i (Local 0 "pj")) λ

        completenessAtStep i = mapInVars (getUpdtVar i) . mapOutVars (getUpdtVar i) $ 
                                quantifyIntermediatePos i φ

        completeness = andList [ completenessAtStep i | i <- [0 .. unum] ]


        orderedPositions = andList $ do 
            i <- [1 .. (unum - 1)]
            let pi = Local (posVarMap M.! i) p
            let pj = Local (posVarMap M.! (i+1)) p
            if dir == LeftToRight then 
                return $ FTestPos Le pi pj
            else
                return $ FTestPos Ge pi pj

        ξ = quantifyList (map (\(_,x,s) -> (x,s, Exists)) $ reverse allVars) $
               andList [correctφ, orderedPositions, completeness]

        iξ = M.delete p iφ
        oξ = oφ


-- the same as "iterOverVar" except we stop *before* the variable pmax
-- given in argument. Note that depending on the direction, this means
-- "before" or "after" in the order of the word ^^.
iterOverVarBeforeLazy :: Direction -> String -> String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVarBeforeLazy dir p pmax (ProgramFormula φ iφ oφ) = ProgramFormula ξ iξ oξ
    where
        -- the number of output variables of φ, i.e., the ones
        -- that can actually *change* by computing φ
        unum :: Int
        unum = M.size oφ

        -- for every number 1 <= i <= unum
        -- we create a Position variable p_i
        iterPosVars :: [(Int, String, Sort)]
        iterPosVars = do
            i <- [1 .. unum]
            return (i, "p_" ++ show i, Pos)

        -- and variables "x_i" for all output variables x of φ
        iterUpdtVars :: [(Int, String, Sort)]
        iterUpdtVars = do
            i <- [1 .. (unum-1)]
            (x, s) <- M.toList oφ
            return (i, x, s)

        -- all quantified vars
        allVars :: [(Int, String, Sort)]
        allVars = iterUpdtVars ++ iterPosVars

        -- allVars as a map from (i, s) to the number of the quantified variable
        updtVarMap :: Map (Int, String) Int
        updtVarMap = M.fromList $ zip (map (\(i, x, _) -> (i, x)) iterUpdtVars) [0..]

        posVarMap  :: Map Int Int
        posVarMap  = M.fromList $ zip (map (\(i, _, _) -> i) iterPosVars) [length iterUpdtVars ..]

        -- finds the corresponding boolean variable
        -- for the variable x at iteration i
        getUpdtVar :: Int -> Int -> String -> Var 
        getUpdtVar 0    depth x = In x
        getUpdtVar n    depth x | n == unum = Out x
        getUpdtVar step depth x = case M.lookup (step, x) updtVarMap of
                                    Just i  -> Local (depth + i) x
                                    Nothing -> error $ "iterUntil: variable " ++ x ++ " not found"

        getPosVar :: Int -> Int -> String -> Var 
        getPosVar step depth x | x == p = case M.lookup step posVarMap of
                                            Just i  -> Local (depth + i) x
                                            Nothing -> error $ "iterUntil: variable " ++ x ++ " not found"
        getPosVar step depth x = In x

        -- Now, we construct the formulas [φ_i] for 0 <= i <= unum - 1
        -- where φ_i is φ with input   variables (updtVarMap i)
        -- and                 output  variables (updtVarMap i+1)
        subφ i = mapInVars (getUpdtVar i) $ 
                    mapOutVars (getUpdtVar (i+1)) $ 
                        mapInVars (getPosVar (i+1)) φ

        correctφ = andList $ [ subφ i | i <- [0 .. unum - 1] ]

        -- condIntermediate => pi < p < p{i+1} 
        -- or                     >   >
        -- with p0 = 0 and pn = p if LTR
        -- p0 = p and pn = +infty otherwise
        condIntermediate LeftToRight 0 x | 0 == unum = FTestPos Lt x (In pmax)
        condIntermediate RightToLeft 0 x | 0 == unum = FTestPos Gt x (In pmax)
        condIntermediate LeftToRight 0 x = 
            FTestPos Lt x (Local (1 + (posVarMap M.! 1)) p)
        condIntermediate RightToLeft 0 x = 
            FTestPos Gt x (Local (1 + (posVarMap M.! 1)) p)
        condIntermediate LeftToRight i x | i == unum = andList [
                FTestPos Gt x (Local (1 + (posVarMap M.! unum)) p)
            ,   FTestPos Lt x (In pmax)
            ]
        condIntermediate RightToLeft i x | i == unum = andList [
                FTestPos Lt x (Local (1 + (posVarMap M.! unum)) p)
            ,   FTestPos Gt x (In pmax)
            ]
        condIntermediate LeftToRight i x = andList [
            FTestPos Lt x (Local (1 + (posVarMap M.! i)) p),
            FTestPos Gt x (Local (1 + (posVarMap M.! (i+1))) p)
            ]
        condIntermediate RightToLeft i x = andList [
            FTestPos Gt x (Local (1 + (posVarMap M.! i)) p),
            FTestPos Lt x (Local (1 + (posVarMap M.! (i+1))) p)
            ]

        -- every position is at most pmax (RTL)
        -- or at least pmax (LTR)
        constraintIntermediatePos = andList $ do 
            j <- [1 .. unum]
            let pj = Local (posVarMap M.! j) p
            if dir == LeftToRight then 
                return $ FTestPos Le pj (In pmax)
            else
                return $ FTestPos Ge pj (In pmax)
        

        quantifyIntermediatePos i λ = quantifyList [("pj", Pos, Forall)] $
                mapInVars (\d x -> if x == p then Local d "pj" else In x) $ 
                    FBin Conj constraintIntermediatePos (
                         FBin Impl (condIntermediate dir i (Local 0 "pj")) λ)


        completenessAtStep i = mapInVars (getUpdtVar i) . mapOutVars (getUpdtVar i) $ 
                                quantifyIntermediatePos i φ

        completeness = andList [ completenessAtStep i | i <- [0 .. unum] ]


        orderedPositions = andList $ do 
            i <- [1 .. (unum - 1)]
            let pi = Local (posVarMap M.! i) p
            let pj = Local (posVarMap M.! (i+1)) p
            if dir == LeftToRight then 
                return $ FTestPos Le pi pj
            else
                return $ FTestPos Ge pi pj

        ξ = quantifyList (map (\(_,x,s) -> (x,s, Exists)) $ reverse allVars) $
               andList [correctφ, orderedPositions, completeness]

        iξ = (M.delete p iφ) `M.union` M.singleton pmax Pos
        oξ = oφ


-- Test if
-- LeftToRight: exists y before pmax
-- RightToLeft: exists y after pmax
-- if the condition holds, call iterOverVarBeforeLazy,
-- otherwise, the program formula is "every input is mapped to the same output"
iterOverVarBefore :: Direction -> String -> String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVarBefore dir p pmax (ProgramFormula φ iφ oφ) = ProgramFormula ξ iξ oξ
    where
        cond = if dir == LeftToRight then FTestPos Lt (Local 0 "y") (In pmax)
                                     else FTestPos Gt (Local 0 "y") (In pmax)
        qcond = quantifyList [("y", Pos, Exists)] cond

        (ProgramFormula θ iθ oθ) = iterOverVarBeforeLazy dir p pmax (ProgramFormula φ iφ oφ)

        identityFormula = andList $ do
            (x, s) <- M.toList oφ
            return $ FBin Equiv (FVar $ Out x) (FVar $ In x)

        ξ = FBin Conj (FBin Impl qcond θ) (FBin Impl (FNot qcond) identityFormula)
        iξ = iθ
        oξ = oθ

-- computeUntil path prog
-- is what happens to the variable once we follow path "path" inside the program "prog"
computeUntil :: [SFP.Movement] -> SFP.ForStmt -> ProgramFormula () 
computeUntil [] stmt = mempty
computeUntil (SFP.MoveIfL _ : xs) (SFP.If b s1 _ ) = ifThenElse b (computeUntil xs s1) (ProgramFormula (FConst False) M.empty M.empty)
computeUntil (SFP.MoveIfR _ : xs) (SFP.If b _  s2) = ifThenElse b (ProgramFormula (FConst False) M.empty M.empty) (computeUntil xs s2)
computeUntil (SFP.MoveSeq 0 : xs) (SFP.Seq ss)   = computeUntil xs (ss !! 0)
computeUntil (SFP.MoveSeq n : xs) (SFP.Seq ss)   = before <> computeUntil xs after
    where
        after = ss !! n
        before = mconcat $ map sfpStmtToProgramFormula $ take (n-1) ss
computeUntil (SFP.MoveFor (PName pm) dirm bsm : xs) (SFP.For (PName p) dir bs stmt) 
    | dirm == dirm && bsm == bs = iterOverVarBefore dir p pm pStmtB <> computeUntil xs stmt
        where
            pStmt  = sfpStmtToProgramFormula stmt
            pStmtB = withNewBoolVars [ x | BName x <- bsm ] pStmt
computeUntil pa pr = error $ "computeUntil: invalid path" ++ show (pa, pr)

computeUntilProg :: SFP.Path -> SFP.ForProgram -> [Var] -> Formula ()
computeUntilProg (SFP.Path (x : path)) (SFP.ForProgram bs stmt) vars = ψ
    where
        pStmt   = computeUntil path stmt
        pStmtB  = withNewBoolVars [ x | BName x <- bs ] pStmt
        φ       = formula pStmtB
        -- now we need to map the variables of the path to variables given as input
        -- to `computeUntilProg`
        -- to that end, we list variables in the path, zip with vars, and remap inputs
        -- to the corresponding variables
        names :: [(Var, String)]
        names   = zip vars . map (\(PName p) -> p) $ SFP.pathPVars (SFP.Path path)
        namesM = M.fromList $ [ (x,y) | (y,x) <- names ]

        ψ = quantInOutVarsGeneric (\n -> M.lookup n namesM) (const Nothing) φ

        


sfpToProgramFormula :: SFP.ForProgram -> ProgramFormula ()
sfpToProgramFormula (SFP.ForProgram bs stmt) = withFalseInputs boolVars $ sfpStmtToProgramFormula stmt
    where 
        boolVars = [ x | BName x <- bs ]

sfpStmtToProgramFormula :: SFP.ForStmt -> ProgramFormula ()
sfpStmtToProgramFormula (SFP.SetTrue (BName x)) = setTrueBoolean x
sfpStmtToProgramFormula (SFP.If b s1 s2) = ifThenElse b (sfpStmtToProgramFormula s1) (sfpStmtToProgramFormula s2)
sfpStmtToProgramFormula (SFP.PrintPos _) = mempty
sfpStmtToProgramFormula (SFP.PrintLbl _) = mempty
sfpStmtToProgramFormula (SFP.Seq ss) = mconcat $ map sfpStmtToProgramFormula ss
sfpStmtToProgramFormula (SFP.For (PName p) dir bs stmt) = iterOverVar dir p subProgram
    where
        boolVars = [ x | BName x <- bs ]
        subProgram = withNewBoolVars boolVars $ sfpStmtToProgramFormula stmt


-- check if there is "a" in the input
verySimpleForProgram :: SFP.ForProgram
verySimpleForProgram = SFP.ForProgram [BName "seen_a"] $ 
    SFP.For (SFP.PName "i") SFP.LeftToRight [] $
        SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
               (SFP.SetTrue $ BName "seen_a")
               (SFP.Seq [])

-- prints all the A’s in the input
verySimpleForProgramPrint :: SFP.ForProgram
verySimpleForProgramPrint = SFP.ForProgram [] $ 
    SFP.For (SFP.PName "i") SFP.LeftToRight [] $
        SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
               (SFP.PrintLbl 'a')
               (SFP.Seq [])

-- check if there is "a" in the input
verySimpleForProgramRev :: SFP.ForProgram
verySimpleForProgramRev = SFP.ForProgram [BName "seen_a"] $ 
    SFP.For (SFP.PName "i") SFP.RightToLeft [] $
        SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
               (SFP.SetTrue $ BName "seen_a")
               (SFP.Seq [])
        
verySimpleForProgramAA :: SFP.ForProgram
verySimpleForProgramAA  = SFP.ForProgram [BName "seen_a1", BName "seen_a2"] $ 
    SFP.For (SFP.PName "i") SFP.LeftToRight [] $
        SFP.Seq [
            SFP.If (SFP.BBin Conj (SFP.BLabelAt (SFP.PName "i") 'a') (SFP.BVar (BName "seen_a1")))
                   (SFP.SetTrue $ BName "seen_a2")
                   (SFP.Seq []),
            SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
                   (SFP.SetTrue $ BName "seen_a1")
                   (SFP.Seq [])
                ]
