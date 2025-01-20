{-# LANGUAGE RecordWildCards #-}
module Logic.ProgramFormulaSpec where 

import SimpleForPrograms

import Logic.Interpretation
import Logic.PullBack
import Logic.Mona
import Logic.ProgramFormula
import Logic.Formulas
import QuantifierFree

import Test.Hspec 

import Control.Monad (forM_)

import qualified Data.Map as M

makeBoolVarsMap :: [String] -> M.Map String Sort
makeBoolVarsMap vs = M.fromList [(x, Boolean) | x <- vs]


f1 :: ProgramFormula String
f1 = ProgramFormula { .. }
  where 
    inputVars = makeBoolVarsMap ["y"]
    outputVars = makeBoolVarsMap ["y", "z", "t"]
    formula = andList [FBin Equiv (FVar (Out "y")) (FConst True)
                      ,FBin Equiv (FVar (Out "z")) (FVar (In "y"))
                      ,FBin Equiv (FVar (Out "t")) (FNot (FVar (In "y")))
                      ]

-- Inputs: "x" and "z"
-- Outputs: "x" "y" "z"
-- x := not x 
-- y := z
-- z := x
f2 :: ProgramFormula String
f2 = ProgramFormula { .. }
    where 
        inputVars = makeBoolVarsMap ["x", "z"]
        outputVars = makeBoolVarsMap ["x", "y", "z"]
        formula = andList [FBin Equiv (FVar (Out "x")) (FNot (FVar (In "x")))
                        ,FBin Equiv (FVar (Out "y")) (FVar (In "z"))
                        ,FBin Equiv (FVar (Out "z")) (FVar (In "x"))
                        ]
-- Composition of f1 and f2 written by hand
-- Inputs: "x" and "z"
-- Outputs: "x" y" "z" "t"
-- x := not x
-- y := y 
-- z := x
-- t := not y
f3 :: ProgramFormula String
f3 = ProgramFormula { .. }
    where 
        inputVars = makeBoolVarsMap ["x", "z"]
        outputVars = makeBoolVarsMap ["x", "y", "z", "t"]
        formula = andList [FBin Equiv (FVar (Out "x")) (FNot (FVar (In "x")))
                          ,FBin Equiv (FVar (Out "y")) (FVar (In "y"))
                          ,FBin Equiv (FVar (Out "z")) (FVar (In "x"))
                          ,FBin Equiv (FVar (Out "t")) (FNot (FVar (In "y")))
                          ]

-- INPUT : "x :: Bool", "p1 :: Pos"
-- OUTPUT : "x :: Bool"
-- If the letter at p1 is equal to 'a', set x to True, otherwise leave x be. 
f4 :: ProgramFormula String
f4 = ProgramFormula { .. }
    where 
        inputVars = M.fromList [("x", Boolean), ("p1", Pos)]
        outputVars = M.fromList [("x", Boolean)]
        formula = FBin Equiv (FVar (Out "x")) (FBin Disj (FLetter (In "p1") 'a') (FVar (In "x")))



checkFormulaRel :: M.Map String Bool -> M.Map String Bool -> ProgramFormula String -> Bool 
checkFormulaRel i o p = evalProgramFormula ProgramFormulaValuation {..} p 
    where 
        valAllTags = []
        valInputWord = [] 
        valPositions = M.empty 
        valTags = M.empty
        valBooleans = M.fromList [(In x, b) | (x, b) <- M.toList i] `M.union` M.fromList [(Out x, b) | (x, b) <- M.toList o]

checkFormulaWord :: M.Map String Bool -> M.Map String Bool -> M.Map String Int -> String -> ProgramFormula String -> Bool
checkFormulaWord i o ps w prog = evalProgramFormula ProgramFormulaValuation {..} prog 
    where 
        valAllTags = []
        valInputWord = w
        valPositions = M.fromList [((In p), v) | (p, v) <- M.toList ps]
        valTags = M.empty
        valBooleans = M.fromList [(In x, b) | (x, b) <- M.toList i] `M.union` M.fromList [(Out x, b) | (x, b) <- M.toList o]


checkFormulaFunction :: M.Map String Bool -> M.Map String Bool -> ProgramFormula String -> Spec
checkFormulaFunction i o f = do 
    it "Should accept the correct output" $ do 
        checkFormulaRel i o f `shouldBe` True
    it "Should not accept any of the incorrect outputs" $ do 
        let incorrectOutput = [M.insert x (not b) o | (x, b) <- M.toList o]
        forM_ incorrectOutput $ \io -> do 
            checkFormulaRel i io f `shouldBe` False

checkFormulaFunctionWord :: M.Map String Bool -> M.Map String Bool -> M.Map String Int -> String -> ProgramFormula String -> Spec
checkFormulaFunctionWord i o ps w f = do 
    it "Should accept the correct output" $ do 
        checkFormulaWord i o ps w f `shouldBe` True
    it "Should not accept any of the incorrect outputs" $ do 
        let incorrectOutput = [M.insert x (not b) o | (x, b) <- M.toList o]
        forM_ incorrectOutput $ \io -> do 
            checkFormulaWord i io ps w f `shouldBe` False


------ PROGRAM 

setBTrue :: ForStmt 
setBTrue = SetTrue (BName "b")

skip :: ForStmt 
skip = Seq [] 

printJ :: ForStmt 
printJ = PrintPos (PName "j")

ifCondition :: BoolExpr 
ifCondition = BBin Conj (BVar (BName "b")) (BTest Eq (PName "i") (PName "j"))

ifBAndEq :: ForStmt
ifBAndEq = If ifCondition  printJ skip

ifAndThenSetTrue :: ForStmt
ifAndThenSetTrue = Seq [ifBAndEq, setBTrue]

forJBackwards :: ForStmt
forJBackwards = For (PName "j") RightToLeft [] ifAndThenSetTrue

forIForwards :: ForStmt
forIForwards = For (PName "i") LeftToRight [BName "b"] forJBackwards

pathToPrint :: [Movement]
pathToPrint = [MoveFor (PName "i") LeftToRight [BName "b"], MoveFor (PName "j") RightToLeft [], MoveSeq 0, MoveIfL ifCondition]



--- Program 2 (compress_as)
setB1True :: ForStmt
setB1True = SetTrue (BName "b1")

setB2True :: ForStmt
setB2True = SetTrue (BName "b2")

setB1B2True :: ForStmt
setB1B2True = Seq [setB1True, setB2True]

ifNotB2SetB1B2True :: ForStmt
ifNotB2SetB1B2True = If (BVar (BName "b2")) skip setB1B2True

ifAThenB2ElseIfNotBSetB1B2True :: ForStmt
ifAThenB2ElseIfNotBSetB1B2True = If (BLabelAt (PName "j") 'a') setB2True ifNotB2SetB1B2True

ifIleJThenIfAEtc :: ForStmt
ifIleJThenIfAEtc = If (BTest Lt (PName "j") (PName "i")) ifAThenB2ElseIfNotBSetB1B2True skip

forJBackwards2 :: ForStmt
forJBackwards2 = For (PName "j") RightToLeft [] ifIleJThenIfAEtc

printI :: ForStmt
printI = PrintPos (PName "i")

printIfB1OrNotA :: ForStmt
printIfB1OrNotA = If (BBin Disj (BVar (BName "b1")) (BNot (BLabelAt (PName "i") 'a'))) printI skip

ifNotB2ThenB1 :: ForStmt
ifNotB2ThenB1 = If (BNot (BVar (BName "b2"))) setB1True skip

forJBackwardsThenPrintAndSkip :: ForStmt
forJBackwardsThenPrintAndSkip = Seq [forJBackwards2, ifNotB2ThenB1, printIfB1OrNotA]

forIForwards2 :: ForStmt
forIForwards2 = For (PName "i") LeftToRight [BName "b1", BName "b2"] forJBackwardsThenPrintAndSkip

compressAsProg :: ForProgram 
compressAsProg = ForProgram [] forIForwards2


compressAsBis :: ForProgram
compressAsBis = ForProgram [] (For (PName "i") LeftToRight [BName "b1",BName "b2"] (Seq [Seq [For (PName "j") RightToLeft [] (If (BTest Lt (PName "j") (PName "i")) (If (BLabelAt (PName "j") 'a') (SetTrue (BName "b2")) (If (BVar (BName "b2")) (Seq []) (Seq [SetTrue (BName "b1"),SetTrue (BName "b2")]))) (Seq [])),If (BNot (BVar (BName "b2"))) (SetTrue (BName "b1")) (Seq [])],If (BBin Disj (BVar (BName "b1")) (BNot (BLabelAt (PName "i") 'a')) ) (PrintPos (PName "i")) (Seq [])]))

seqseq :: ForStmt
seqseq = Seq [Seq [For (PName "j") RightToLeft [] (If (BTest Lt (PName "j") (PName "i")) (If (BLabelAt (PName "j") 'a') (SetTrue (BName "b2")) (If (BVar (BName "b2")) (Seq []) (Seq [SetTrue (BName "b1"),SetTrue (BName "b2")]))) (Seq [])),If (BNot (BVar (BName "b2"))) (SetTrue (BName "b1")) (Seq [])],If (BBin Disj (BVar (BName "b1")) (BNot (BLabelAt (PName "i") 'a')) ) (PrintPos (PName "i")) (Seq [])]

pathToPrint2 :: [Movement]
pathToPrint2 = [MoveFor (PName "i") LeftToRight [BName "b1",BName "b2"],MoveSeq 2,MoveIfL (BBin Disj (BVar (BName "b1")) (BNot (BLabelAt (PName "i") 'a')))]


--- PRINT UNTIL BACKWARDS --- 
printUntilABackwards :: ForProgram
printUntilABackwards = ForProgram [BName "b"] forBack
    where
        forBack      = For (PName "i") RightToLeft [] (Seq [printAorKeep, setBIfA])
        printAorKeep = If (BVar (BName "b"))  (PrintLbl 'a') (PrintPos (PName "i"))
        setBIfA      = If (BLabelAt (PName "i") 'a') setBTrue skip

-- There are consecutive As
thereAreConsecutiveAsFormula :: Formula ()
thereAreConsecutiveAsFormula = quantifyList [("i", Pos, Exists), ("j", Pos, Exists)] $ andList [consecutive, iLessThanJ, labelledAs]
    where
        iLessThanJ = FTestPos Lt (Local 1 "i") (Local 0 "j")
        consecutive = FNot . quantifyList [("k", Pos, Exists)] . andList $ [
            FTestPos Lt (Local 2 "i") (Local 0 "k"),
            FTestPos Lt (Local 0 "k") (Local 1 "j") ]
        labelledAs = andList [FLetter (Local 0 "i") 'a', FLetter (Local 1 "j") 'a']
        




spec :: Spec
spec = do
    describe "The composition works" $ do 
        let f12 = f1 <> f2 
        it "Should have correct input variables" $ do 
            -- keys of inputVars f12 should be ["y", "x", "z"] (possibly shuffled)
            let i1 = M.keys (inputVars f12)
            let i2 = ["y", "x"]
            i1 `shouldMatchList` i2
        it "Should have correct output variables" $ do
            -- keys of outputVars f12 should be ["y", "z", "t", "x"] (possibly shuffled)
            let i1 = M.keys (outputVars f12)
            let i2 = ["y", "z", "t", "x"]
            i1 `shouldMatchList` i2
        describe "The composition should return correct results" $ do 
            let i1 = M.fromList [("x", True), ("y", False)]
            let o1 = M.fromList [("x", False), ("y", False), ("z", True), ("t", True)]
            checkFormulaFunction i1 o1 f12
    describe "iterateOverVar works" $ do 
        let f4iter = iterOverVar LeftToRight "p1" f4
        it "Should have correct input variables" $ do 
            -- keys of inputVars f4iter should be ["x", "p1"] (possibly shuffled)
            let i1 = M.keys (inputVars f4iter)
            let i2 = ["x"]
            i1 `shouldMatchList` i2
        it "Should have correct output variables" $ do
            -- keys of outputVars f4iter should be ["x"] (possibly shuffled)
            let i1 = M.keys (outputVars f4iter)
            let i2 = ["x"]
            i1 `shouldMatchList` i2
        describe "The iteration should return correct result for a word containing a" $ do 
            let w = "bbbaababb"
            let i1 = M.fromList [("x", False)]
            let o1 = M.fromList [("x", True)]
            checkFormulaFunctionWord i1 o1 M.empty w f4iter
            let i2 = M.fromList [("x", True)]
            let o2 = M.fromList [("x", True)]
            checkFormulaFunctionWord i2 o2 M.empty w f4iter
        describe "The iteration should return correct result for a word not containing a" $ do
            let w = "bbbbb"
            let i1 = M.fromList [("x", False)]
            let o1 = M.fromList [("x", False)]
            checkFormulaFunctionWord i1 o1 M.empty w f4iter
            let i2 = M.fromList [("x", True)]
            let o2 = M.fromList [("x", True)]
            checkFormulaFunctionWord i2 o2 M.empty w f4iter
        -- describe "The simple program works" $ do
        --     runIO $ putStrLn $ printProgramFormulaGeneric (sfpStmtToProgramFormula forIForwards)
        --     runIO $ putStrLn $ printProgramFormulaGeneric (computeUntil pathToPrint forIForwards)
        --     runIO $ putStrLn $ printProgramFormulaGeneric $ withNewBoolVars ["b"] (computeUntil (tail pathToPrint) forJBackwards)
        --     runIO $ putStrLn $ printProgramFormulaGeneric (computeUntil (tail pathToPrint) forJBackwards)
        --     runIO $ putStrLn $ printProgramFormulaGeneric (computeUntil (tail (tail pathToPrint)) ifAndThenSetTrue) 
        --     it "fails" $ do 
        --         True `shouldBe` False



