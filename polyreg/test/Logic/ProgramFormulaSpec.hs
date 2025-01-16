{-# LANGUAGE RecordWildCards #-}
module Logic.ProgramFormulaSpec where 

import SimpleForPrograms

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



