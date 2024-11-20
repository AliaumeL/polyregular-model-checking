module TwoSortedFormulaSpec where

import Test.Hspec
import Test.QuickCheck

import TwoSortedFormulas
import QuantifierFree


spec :: Spec
spec = do
    describe "The evaluator for FO Formulas (TwoSortedFormulas.evalFormula)" $ do
        it "Correctly implements true" $ property $
            \x -> (evalFormula x [] FTrue == True)
        it "Correctly implements false" $ property $
            \x -> (evalFormula x [] FFalse == False)
