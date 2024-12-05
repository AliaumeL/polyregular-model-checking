module ReductionLitEqSpec where

import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import ForProgramsTyping
import Parser.ParseHighLevel
import ReductionLitEq

fromRight' :: (Show b, Show a) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight': " ++ show e

untypeProgram :: Program String a -> Program String ()
untypeProgram = fmap (const ())

spec :: Spec
spec = do 
    testProgram <- runIO $ parseFromFile "assets/litteral_test.pr"
    let infered = fromRight' (inferProgram (fromRight' testProgram))
    describe "We actually remove literal tests calls" $ do
        it "Starts with a program with some BLitEq calls" $ do 
            (hasLitEq infered) `shouldBe` True
        it "Ends with a program without function calls" $ do
            let eliminated = removeBLitEq infered
            (hasLitEq eliminated) `shouldBe` False
        it "The program still works" $ do
            let eliminated = removeBLitEq infered
            let input = "go to park"
            let expected = runProgramString (untypeProgram infered)    input
            let actual = runProgramString   (untypeProgram eliminated) input
            actual `shouldBe` expected


