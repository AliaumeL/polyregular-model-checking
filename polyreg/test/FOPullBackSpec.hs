module FOPullBackSpec where

import Test.Hspec
import Test.QuickCheck

import FOPullBack 
import qualified FOInterpretation as FOI
import qualified TwoSortedFormulas as TSF
import qualified FOInterpretationSpec as FOISpec
import QuantifierFree

type Var  = String
type Alph = Char
type Tag  = String

aStarBstarTSF = inject FOISpec.formulaAstarBstar

spec :: Spec
spec = do
    describe "The injection of FO into TwoSortedFO (FOPullBack.inject)" $ do
        it "Correctly pulls back a^* b^*" $ property $
            \x -> TSF.evalFormula x [] aStarBstarTSF == FOI.evalFormula FOISpec.formulaAstarBstar x
