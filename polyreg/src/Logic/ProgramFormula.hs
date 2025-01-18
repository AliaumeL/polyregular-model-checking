{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Logic.ProgramFormula where

import qualified SimpleForPrograms as SFP
import SimpleForPrograms (Direction(..), BName(..), PName(..), Movement(..))

import Data.Map (Map)
import qualified Data.Map as M

import Logic.Formulas
import QuantifierFree

import Debug.Trace

import Control.Monad (guard)

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
        φ' = quantInOutVarsGeneric (\_ x -> Just $ In ("in_" ++ x)) (\_ x -> Just $ In ("out_" ++ x)) φ
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
        f _ y = if x == y then (Just $ Local 0 y) else Nothing

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

            fφ :: Sort -> String -> Maybe Var
            fφ _ x = case M.lookup x commonVarsQ of
                        Just i   -> Just $ Local i x
                        Nothing  -> Nothing

            fψ :: Sort -> String -> Maybe Var
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


ifThenElse :: Formula tag -> ProgramFormula tag  -> ProgramFormula tag  -> ProgramFormula tag 
ifThenElse θ (ProgramFormula φ iφ oφ) (ProgramFormula ψ iψ oψ) = ProgramFormula ξ iξ oξ
    where
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

        iξ = iφ `M.union` iψ `M.union` iθ `M.union` missingOutputφ `M.union` missingOutputψ 

        oξ = totalOutputVars


iterOverVarNew :: Direction -> String -> Maybe Var -> ProgramFormula tag  -> ProgramFormula tag
iterOverVarNew dir p bound (ProgramFormula φ iφ oφ) = finalOutput
    where
        -- We assume that we are not using an empty iteration: 
        --   a. the word is not empty
        --   b. the bound (if it exists) is not defining the empty subword
        --   c. that there is *some* modification. Otherwise, it is the identity
        --
        -- 1. We first compute all "static" input variables, that will
        --    be passed to the formula φ at every step of the for loop 
        --    they can be boolean OR position variables
        static :: Map String Sort
        static = iφ `M.difference` oφ
        -- 2. We then compute all the "updatable" variables, that will
        --    that are (potentially) modified by φ at every step of the
        --    loop. All output variables are potentially modified by φk
        updatable :: Map String Sort
        updatable = oφ
        -- 3. The new input vars are  => the previous ones - p + bound (if bound is an input var)
        inBoundVar :: Map String Sort
        inBoundVar = case bound of 
                        Just (In x) -> M.fromList [(x, Pos)]
                        _           -> M.empty
        iξ = inBoundVar `M.union` M.delete p iφ `M.union` M.delete p updatable
        -- 4. The new output vars are => the same as before
        oξ = oφ
        -- For the actual content of the formula ξ, we do the following
        --
        -- a. We existentially quantify
        --    over |oφ| - 1 intermediate states (copies of the output variables)
        -- b. We existentially quantify 
        --    over |oφ|     position variables  (instances for p)
        -- c. We then say that 
        --   - the position variables are ordered (p1 <= p2 <= ... <= pn) (if LeftToRight)
        --   - the position variables respect the bound (if it exists)
        --   - the program formula φ, with *modified* variables
        --     bound to the intermediate states, is correct for every step
        --   - for every step, for every *new* position variable 
        --      "pj" between "pi" and "pi+1", the formula φ 
        --      does not change the "updatableVariables"
        --
        -- To that end, we have a function φAtStep
        -- that considers a position variable "pj",
        -- and two functions that tell which are the input / output
        -- updatable variables at this precise time. 
        -- φAtStep :: Var -> (String -> Maybe Var) -> (String -> Maybe Var) -> Formula tag
        φAtStep pj iUpd oUpd = quantInOutVarsGeneric qIn qOut φ
            where
                qIn Pos n | n == p = Just pj
                qIn Pos _          = Nothing
                qIn Boolean x      = iUpd x
                qOut Boolean x     = oUpd x
                qOut _       _     = Nothing
        -- To decide how many position variables / intermediate states we need
        -- it suffices to consider the size of "updatable" variables
        maxUpdates :: Int
        maxUpdates = M.size updatable
        -- Now, we can build position variables and intermediate states
        -- with the format
        -- (step number, var_name, quant)
        posVars :: [(Int, String, Sort)]
        posVars = do
            i <- [1 .. maxUpdates]
            return (i, p ++ "_" ++ show i, Pos)
        updtVars :: [(Int, String, Sort)]
        updtVars = do
            i <- [1 .. (maxUpdates - 1)]
            (x, s) <- M.toList updatable
            return (i, x, s)
        updtVarsReverse :: Map (Int, String) Int
        updtVarsReverse = M.fromList $ zip (reverse (map (\(i, x, _) -> (i, x)) updtVars)) [0..]
        allVars :: [(Int, String, Sort)]
        allVars = posVars ++ [ (i, b ++ "_" ++ show i, s) | (i,b,s) <-  updtVars ]
        -- In order to be able to actually *use* these variables
        -- in our formula, we need to be able to find them.
        -- We assume that allVars will be quantified existentially in this specific ordering.
        -- We create a function 
        -- posAtStep :: Int -> Var
        --      it maps a step (from 1 to maxUpdates) to the corresponding position variable
        posAtStep :: Int -> Var
        posAtStep i = Local varPosFromEnd (p ++ "_" ++ show i)
            where
                varPosFromEnd = length updtVars + length posVars - i
        -- updtAtStep :: Int -> String -> Var 
        --      it maps a step (from 0 to maxUpdates) to the corresponding boolean variable
        --      note that at step 0           => these are the input  variables
        --      at step           maxUpdates  => these are the output variables
        --
        -- Note: can fail, but should not!
        updtAtStep :: Int -> String -> Var
        updtAtStep i b | i == 0             = In  b
        updtAtStep i b | i == maxUpdates    = Out b
        updtAtStep i b                      = Local (updtVarsReverse M.! (i, b)) (b ++ "_" ++ show i)
        updtAtStepSafe :: Int -> Sort -> String -> Maybe Var
        updtAtStepSafe i s b = do 
            guard  $ s == Boolean
            guard  $ b `M.member` updatable
            return $ updtAtStep i b
        -- Now, we can say that the transformation between steps i and i+1
        -- for 0 <= i <= maxUpdates is correct. I.e.,
        -- that (In boools + p1) φ (bools 1 + p2) φ (bools 2) ... φ (Out bools)
        -- is true.
        -- correctAtStep :: Int -> Formula tag
        correctAtStep i = φAtStep (posAtStep (i+1)) (updtAtStepSafe i Boolean) (updtAtStepSafe (i+1) Boolean)
        -- Now, we can say that everything is correct
        correct = andList [ correctAtStep i | i <- [0 .. (maxUpdates-1)] ]
        -- Let us now turn our attention to completeness
        -- To be complete, we need to prove that every 
        -- intermediate "position" would not modify the computation
        -- I.e., that φAtStep (p_j) (bools_i) (bools_i) holds
        -- for every p_j that is (strictly) between p_i and p_{i+1}
        -- Note: to not mess the De Bruijn indices, we first
        -- quantify the local variable "pj" before doing the substitution
        -- We are now ready to say that the step "i" is complete.
        -- completenessAtStep :: Int -> Formula tag
        completenessAtStep i = quantifyList [(p ++ "_j", Pos, Forall)] (FBin Impl rangeQ φInRange)
            where
                φInRange = φAtStep (Local 0 (p ++ "_j")) updtAtStepShifted updtAtStepShifted
                rangeQ   = condIntermediate dir bound i (Local 0 (p ++ "_j"))
                updtAtStepShifted x = fmap (shiftVar 1) $ updtAtStepSafe i Boolean x
        -- We can now say that the whole program is complete
        -- completeness :: Formula tag
        completeness = andList [ completenessAtStep i | i <- [0 .. maxUpdates] ]
        -- We can now say what is the "intermediate condition"
        -- the order depends on the direction 
        -- Check LeftToRight first
        --      i.e. "pi < p_j < p_{i+1}" 
        --      p0   = -infinity
        --      pmax = +infinity or bound
        -- Check RightToLeft 
        --      pi > p_j > p_{i+1}  
        --      p0   = -infinity or the bound 
        --      pmax = +infinity
        -- condIntermediate :: Direction -> Maybe Var -> Int -> Var -> Formula tag
        condIntermediate LeftToRight _         0 x = FTestPos Lt x (shiftVar 1 (posAtStep 1))
        condIntermediate LeftToRight Nothing   i x | i == maxUpdates = FTestPos Gt x (shiftVar 1 (posAtStep i))
        condIntermediate LeftToRight (Just v)  i x | i == maxUpdates = andList [
                        FTestPos Gt x (shiftVar 1 (posAtStep i)),
                        FTestPos Lt x v
                    ]
        condIntermediate LeftToRight _         i x = andList [
                        FTestPos Gt x (shiftVar 1 (posAtStep i)),
                        FTestPos Lt x (shiftVar 1 (posAtStep (i+1)))
                    ]
        condIntermediate RightToLeft _        0 x = FTestPos Lt x (shiftVar 1 (posAtStep 1))
        condIntermediate RightToLeft Nothing  i x | i == maxUpdates = FTestPos Lt x (shiftVar 1 (posAtStep i))
        condIntermediate RightToLeft (Just v) i x | i == maxUpdates = andList [
                        FTestPos Lt x (shiftVar 1 (posAtStep i)),
                        FTestPos Gt x v
                    ]
        condIntermediate RightToLeft _        i x = andList [
                        FTestPos Lt x (shiftVar 1 (posAtStep i)),
                        FTestPos Gt x (shiftVar 1 (posAtStep (i+1)))
                    ]


        -- orderOfPositions :: Direction -> Formula tag
        orderOfPositions LeftToRight = andList $ do 
            i <- [1 .. (maxUpdates - 1)]
            let pi = posAtStep i
            let pj = posAtStep (i+1)
            return $ FTestPos Le pi pj
        orderOfPositions RightToLeft = andList $ do
            i <- [1 .. (maxUpdates - 1)]
            let pi = posAtStep i
            let pj = posAtStep (i+1)
            return $ FTestPos Ge pi pj

        -- positionsAreBelowBound :: Direction -> Maybe Var -> Formula tag
        positionsAreBelowBound _            Nothing = FConst True
        positionsAreBelowBound LeftToRight (Just v) = FTestPos Lt (posAtStep maxUpdates) v
        positionsAreBelowBound RightToLeft (Just v) = FTestPos Gt (posAtStep maxUpdates) v

        ξnonEmpty = quantifyList (map (\(_,x,s) -> (x,s, Exists)) allVars) $
                       andList [correct, orderOfPositions dir, completeness, positionsAreBelowBound dir bound]
        nonEmptyWord = quantifyList [("k", Pos, Exists)] $ FConst True
        finalOutput = ifThenElse nonEmptyWord (ProgramFormula ξnonEmpty iξ oξ) mempty








iterOverVar :: Direction -> String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVar _   _      (ProgramFormula φ iφ oφ) | M.size oφ == 0 = mempty
iterOverVar dir p prog = iterOverVarNew dir p Nothing prog


-- the same as "iterOverVar" except we stop *before* the variable pmax
-- given in argument. Note that depending on the direction, this means
-- "before" or "after" in the order of the word ^^.
iterOverVarBeforeLazy :: Direction -> String -> String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVarBeforeLazy _   _ _   (ProgramFormula φ iφ oφ) | M.size oφ == 0 = mempty
iterOverVarBeforeLazy dir p pmax prog = ifThenElse nonEmptyRange (iterOverVarNew dir p (Just $ In pmax) prog) mempty
    where
        nonEmptyRange = case dir of 
                            LeftToRight -> quantifyList [("k", Pos, Exists)] $ FTestPos Lt (Local 0 "k") (In pmax)
                            RightToLeft -> quantifyList [("k", Pos, Exists)] $ FTestPos Gt (Local 0 "k") (In pmax)

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
computeUntil (SFP.MoveIfL _ : xs) (SFP.If b s1 _ ) = ifThenElse (boolExprToFormula b) (computeUntil xs s1) (ProgramFormula (FConst False) M.empty M.empty)
computeUntil (SFP.MoveIfR _ : xs) (SFP.If b _  s2) = ifThenElse (boolExprToFormula b) (ProgramFormula (FConst False) M.empty M.empty) (computeUntil xs s2)
computeUntil (SFP.MoveSeq 0 : xs) (SFP.Seq ss)   = computeUntil xs (ss !! 0)
computeUntil (SFP.MoveSeq n : xs) (SFP.Seq ss)   = before <> computeUntil xs after
    where
        after = ss !! n
        before = mconcat $ map sfpStmtToProgramFormula $ take (n-1) ss
computeUntil (SFP.MoveFor (PName pm) dirm bsm : xs) (SFP.For (PName p) dir bs stmt) 
    | dirm == dirm && bsm == bs = iterOverVarBefore dir p pm pStmtB <> reminder
        where
            pStmt  = sfpStmtToProgramFormula stmt
            pStmtB = withNewBoolVars [ x | BName x <- bsm ] pStmt
            reminder = withNewBoolVars [ x | BName x <- bsm ] $ computeUntil xs stmt
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

        getNewName :: Sort -> String -> Maybe Var 
        getNewName s n = do
            guard $ s == Pos
            M.lookup n namesM

        ψ = quantInOutVarsGeneric getNewName (\_ _ -> Nothing) φ

        


sfpToProgramFormula :: SFP.ForProgram -> ProgramFormula ()
sfpToProgramFormula (SFP.ForProgram bs stmt) = withFalseInputs boolVars $ sfpStmtToProgramFormula stmt
    where 
        boolVars = [ x | BName x <- bs ]

sfpStmtToProgramFormula :: SFP.ForStmt -> ProgramFormula ()
sfpStmtToProgramFormula (SFP.SetTrue (BName x)) = setTrueBoolean x
sfpStmtToProgramFormula (SFP.If b s1 s2) = ifThenElse (boolExprToFormula b) (sfpStmtToProgramFormula s1) (sfpStmtToProgramFormula s2)
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
