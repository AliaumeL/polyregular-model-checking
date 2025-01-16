{-# LANGUAGE RecordWildCards #-}
module Logic.ProgramFormulaSpec where 

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

checkFormulaRel :: M.Map String Bool -> M.Map String Bool -> ProgramFormula String -> Bool 
checkFormulaRel i o p = evalProgramFormula ProgramFormulaValuation {..} p 
    where 
        valAllTags = []
        valInputWord = [] 
        valPositions = M.empty 
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

spec :: Spec
spec = 
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

