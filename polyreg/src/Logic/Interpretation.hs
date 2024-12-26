{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Interpretation where

import Logic.Formulas
import QuantifierFree
import Logic.ProgramFormula (computeUntil)
import qualified Logic.ProgramFormula as PF
import qualified SimpleForPrograms as SFP
import SimpleForPrograms (Movement(..))


data Interpretation tag = Interpretation {
    tags       :: [tag],
    alphabet   :: String,
    domain     :: tag -> [String] -> Formula tag,
    order      :: tag -> tag -> [String] -> [String] -> Formula tag,
    -- TODO: remove [String] from label and copy: it is useless
    label      :: tag -> Char -> [String] -> Formula tag,
    copy       :: tag -> Int  -> [String] -> Formula tag,
    arity      :: tag -> Int,
    maxArity   :: Int
}


-- tags      = program positions 
-- alphabet  = all strings in the program
-- domain    = whether the program position should be considered
--      => existentially quantify the output of PF.computeUntil position
-- order     = comparing two positions, this is simply a mix of legicographic
-- label     = if a position is a print statement
-- copy      = if a position is a copy statement
-- arity     = how many for loop variables are visible on this position
-- maxArity  = max of arities over positions

normalizeMovement :: Movement -> Movement
normalizeMovement (MoveIfL _) = MoveSeq 0
normalizeMovement (MoveIfR _) = MoveSeq 1
normalizeMovement (MoveSeq n) = MoveSeq n
normalizeMovement (MoveFor p d b) = MoveFor p d b


-- whether "x" `happensBefore` "y"
-- input variables  are taken from the left  movement,
-- output variables are taken from the right movement
happensBefore :: [Movement] -> [Movement] -> Formula ()
happensBefore [] [] = FConst True
happensBefore (MoveSeq i : ms) (MoveSeq j : ns) 
    | i < j = FConst True
    | i > j = FConst False
    | otherwise = happensBefore ms ns
happensBefore (MoveFor p SFP.LeftToRight _ : ms) (MoveFor q SFP.LeftToRight _ : ns) = 
    andList [FTestPos Le (In p) (Out q), happensBefore ms ns]
happensBefore (MoveFor p SFP.RightToLeft _ : ms) (MoveFor q SFP.RightToLeft _ : ns) =
    andList [FTestPos Ge (In p) (Out q), happensBefore ms ns]
happensBefore _ _ = error $ "happensBefore: incompatible movements"


-- labelFormula
labelFormula :: SFP.ForStmt -> Char -> [String] -> Formula ()
labelFormula (SFP.PrintLbl c) c' _ = FConst $ c == c'
labelFormula _ _ _ = FConst False

-- copyFormula
copyFormula :: SFP.ForStmt -> Int -> [String] -> Formula ()
copyFormula (SFP.PrintPos (SFP.PName p)) i ps = FConst $ ps !! i == p
copyFormula _ _ _ = FConst False

toInterpretation :: SFP.ForProgram -> Interpretation SFP.Path
toInterpretation prog = Interpretation tags alphabet domain order label copy arity maxArity
    where
        -- print positions
        tags = SFP.listPrintStatements prog
        -- all characters in the program
        alphabet = SFP.listAlphabet prog
        -- print statements
        label = \tag c vars -> labelFormula tag c vars
        copy = \tag i vars -> copyFormula tag i vars
        -- domain formula => compute until + exists
        domain = \tag vars -> PF.computeUntil tag prog vars
        -- order formula -> happens before
        order = \(SFP.Path p1) (SFP.Path p2) vars1 vars2 -> happensBefore p1 p2
        -- arities
        arity = length . SFP.pathPVars
        maxArity = maximum $ map arity $ tags


{-

evalInterpretation :: Interpretation String -> String -> String
evalInterpretation interp word = map (\(_,_,c) -> c) $ positionsFilteredSortedWithChars
    where
        comparePositions :: (String, [Int]) -> (String, [Int]) -> Ordering
        comparePositions (t1,p1) (t2,p2) = if t1 == t2 && p1 == p2 then 
                                            EQ
                                           else case cmp of 
                                            True -> LT
                                            False -> GT
            where
                vars1 = map (\i -> "x" ++ show i) [0..length p1 -1]
                vars2 = map (\i -> "y" ++ show i) [0..length p2 -1]
                vars  = vars1 ++ vars2
                state = FormulaState (Map.fromList $ zip vars (p1 ++ p2)) word
                cmp = evalFormulaInContext state $ orderFormula interp t1 t2 vars1 vars2

        computePresence :: (TagName, [Int]) -> Bool
        computePresence (tag, pos) = evalFormulaInContext state $ domainFormula interp tag vars
            where
                vars = map (\i -> "x" ++ show i) [0..length pos - 1]
                state = FormulaState (Map.fromList $ zip vars pos) word

        computeChar :: (TagName, [Int]) -> Char
        computeChar (tag, pos) = fst . head . filter snd $ shouldCopy ++ letters
            where
                vars = map (\i -> "x" ++ show i) [0..length pos - 1]
                state = FormulaState (Map.fromList $ zip vars pos) word

                shouldCopy :: [(Char, Bool)]
                shouldCopy = do 
                    i <- [0..length pos - 1]
                    let c = word !! (pos !! i)
                    return $ (c, evalFormulaInContext state $ copyFormula interp tag i vars)

                letters :: [(Char, Bool)]
                letters    = do 
                    c <- outputLetters interp
                    return $ (c, evalFormulaInContext state $ labelFormula interp tag c vars)
                    

        positionsTag :: TagName -> [[Int]]
        positionsTag tag = 
            let n = arity interp tag
            in  sequence $ replicate n [0..length word - 1]

        positions :: [(TagName, [Int])]
        positions = concatMap (\tag -> map (\pos -> (tag, pos)) $ positionsTag tag) $ tags interp

        positionsFiltered :: [(TagName, [Int])]
        positionsFiltered = filter computePresence positions

        
        positionsFilteredSorted :: [(TagName, [Int])]
        positionsFilteredSorted = sortBy comparePositions positionsFiltered


        positionsFilteredSortedWithChars :: [(TagName, [Int], Char)]
        positionsFilteredSortedWithChars = do
            (tag, pos) <- positionsFilteredSorted
            return (tag, pos, computeChar (tag, pos))
-}
