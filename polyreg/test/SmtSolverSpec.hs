module SmtSolverSpec where

import Test.Hspec

import SmtSolver
import QuantifierFree
import qualified TwoSortedFormulas as TSF
import qualified FOInterpretation as FOI
import qualified FOInterpretationSpec as FOISpec
import qualified FOPullBack as PB

trueFile :: String
trueFile = unlines [
    "m2l-str;",
    "true;" ]

falseFile :: String
falseFile = unlines [
    "m2l-str;",
    "false;" ]

oneAoneB :: TSF.Formula String Char
oneAoneB = TSF.FBin Conj oneA oneB
    where
        oneA = TSF.FQuant TSF.Exists "x" TSF.Pos (TSF.FLetter "x"  'a')
        oneB = TSF.FQuant TSF.Exists "y" TSF.Pos (TSF.FLetter "y"  'b')

duplicateAsBs :: TSF.Formula String Char
duplicateAsBs = PB.runPullBack FOISpec.duplicateFOI FOISpec.formulaAstarBstar

reverseAsBs :: TSF.Formula String Char
reverseAsBs = PB.runPullBack FOISpec.reverseFOI FOISpec.formulaAstarBstar

asThenBsThenAsAsBs :: TSF.Formula String Char
asThenBsThenAsAsBs = PB.runPullBack FOISpec.asThenBsThenAsFOI FOISpec.formulaAstarBstar

spec :: Spec
spec = do 
    describe "One can run MONA" $ do 
        it "Runs MONA on a True file" $ do 
            runMona trueFile `shouldReturn` Sat
        it "Runs MONA on a False file" $ do 
            runMona falseFile `shouldReturn` Unsat
    describe "Mona, when input contains one a and one b" $ do 
        it "Accepts that it is possible" $ do 
            (runMona (encodeMona "ab" ["A"] oneAoneB)) `shouldReturn` Sat
        it "Accepts that the duplicate cannot be in a*b*" $ do
            (runMona (encodeMona "ab" (FOI.tags FOISpec.duplicateFOI) (TSF.FBin Conj oneAoneB duplicateAsBs))) `shouldReturn` Unsat
        it "Accepts that the reverse can be in a*b*" $ do
            (runMona (encodeMona "ab" (FOI.tags FOISpec.reverseFOI) (TSF.FBin Conj oneAoneB reverseAsBs))) `shouldReturn` Sat
        it "Accepts that the asThenBsThenAs cannot be in a*b*" $ do
            (runMona (encodeMona "ab" (FOI.tags FOISpec.asThenBsThenAsFOI) (TSF.FBin Conj oneAoneB asThenBsThenAsAsBs))) `shouldReturn` Unsat
        
