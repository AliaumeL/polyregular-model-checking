{-# LANGUAGE RecordWildCards #-}
module Logic.ProgramFormulaSpec where 

import Logic.ProgramFormula
import Logic.Formulas
import QuantifierFree

import Test.Hspec 

import Control.Monad (forM)

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
checkFormulaRel = undefined 

checkFormulaFunction :: M.Map String Bool -> M.Map String Bool -> ProgramFormula String -> Spec () 
checkFormulaFunction i o f = do 
    it "Should accept the correct output" $ do 
        checkFormulaRel i o f `shouldBe` True
    it "Should not accept any of the incorrect outputs" $ do 
        let incorrectOutput = [o `M.insert` (x, not b) | (x, b) <- M.toList o]
        forM incorrectOutput $ \io -> do 
            checkFormulaRel i io f `shouldBe` False






spec :: Spec () 
spec 

