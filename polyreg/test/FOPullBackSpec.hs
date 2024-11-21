module FOPullBackSpec where

import Test.Hspec
import Test.QuickCheck

import FOPullBack 
import qualified FOInterpretation as FOI
import qualified TwoSortedFormulas as TSF
import FOInterpretation (Formula(..))
import qualified FOInterpretationSpec as FOISpec
import QuantifierFree
import Debug.Trace

type Var  = String
type Alph = Char
type Tag  = String

aStarBstarTSF :: TSF.Formula String Char
aStarBstarTSF = inject FOISpec.formulaAstarBstar

evalPullBack :: FOI.FOInterpretation Var Alph Tag -> Formula Tag Alph -> String -> Bool
evalPullBack i f w = TSF.evalFormula w (FOI.tags i) (runPullBack i f)


spec :: Spec
spec = do
    describe "The injection of FO into TwoSortedFO (FOPullBack.inject)" $ do
        it "Correctly injects a^* b^*" $ property $
            \x -> TSF.evalFormula x [] aStarBstarTSF `shouldBe` FOI.evalFormula FOISpec.formulaAstarBstar x
    describe "The pullback of True/False through (FOPullBack.pullBack)" $ do
        it "Leaves True untouched for the identity interpretation" $ property $
            \x -> evalPullBack FOISpec.identityFOI FOTrue x `shouldBe` True
        it "Leaves True untouched for the reverse interpretation" $ property $
            \x -> evalPullBack FOISpec.reverseFOI FOTrue x `shouldBe` True
        it "Leaves True untouched for the duplicate interpretation" $ property $
            \x -> evalPullBack FOISpec.duplicateFOI FOTrue x `shouldBe` True
        it "Leaves True untouched for the squaring interpretation" $ property $
            \x -> evalPullBack FOISpec.squaringFOI FOTrue x `shouldBe` True
    describe "The pullback of a^*b^* through (FOPullBack.pullBack)" $ do
        it "Works for the identity function" $ property $
            \x -> evalPullBack FOISpec.identityFOI FOISpec.formulaAstarBstar x `shouldBe` FOISpec.aStarBStar x
        it "Works for the duplicate function" $ property $
            \x -> evalPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar x `shouldBe` FOISpec.aStarBStar (x ++ x)
        it "Works for the duplicate function (specific examples)" $ do
            evalPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar "aaa" `shouldBe` True
            evalPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar "bbb" `shouldBe` True
            evalPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar "ba" `shouldBe` False
            evalPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar "ab" `shouldBe` False
        it "Works for the reverse function (specific examples)" $ do
            evalPullBack FOISpec.reverseFOI FOISpec.formulaAstarBstar "ba" `shouldBe` True
            evalPullBack FOISpec.reverseFOI FOISpec.formulaAstarBstar "ab" `shouldBe` False
        it "Works for the reverse function" $ property $
            \x -> evalPullBack FOISpec.reverseFOI FOISpec.formulaAstarBstar x `shouldBe` FOISpec.aStarBStar (reverse x)
        it "Works for the squaring function (specific examples)" $ do
            evalPullBack FOISpec.squaringFOI FOISpec.formulaAstarBstar "aaa" `shouldBe` True
            evalPullBack FOISpec.squaringFOI FOISpec.formulaAstarBstar "bbb" `shouldBe` True
            evalPullBack FOISpec.squaringFOI FOISpec.formulaAstarBstar "ab" `shouldBe`  False
            evalPullBack FOISpec.squaringFOI FOISpec.formulaAstarBstar "ba" `shouldBe`  False
        it "Works for the squaring function" $ property $
            \x -> evalPullBack FOISpec.squaringFOI FOISpec.formulaAstarBstar x `shouldBe` FOISpec.aStarBStar (FOISpec.squaring x)
        it "Works for the asThenBsThenAs function" $ property $
            \x -> evalPullBack FOISpec.asThenBsThenAsFOI FOISpec.formulaAstarBstar x `shouldBe` FOISpec.aStarBStar (FOISpec.asThenBsThenAs x)
