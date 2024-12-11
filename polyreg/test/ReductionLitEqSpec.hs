module ReductionLitEqSpec where

import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import ForProgramsTyping
import Typing.Inference (inferAndCheckProgram)
import Parser.ParseHighLevel
import ReductionLitEq

fromRight' :: (Show b, Show a) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight': " ++ show e

untypeProgram :: Program String a -> Program String ()
untypeProgram = fmap (const ())

spec :: Spec
spec = do 
    describe "We actually remove literal tests calls on `litteral_test`" $ do
        testProgram <- runIO $ parseFromFile "assets/litteral_test.pr"
        let infered = fromRight' (inferAndCheckProgram (fromRight' testProgram))
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
    describe "We actually remove literal tests calls on `bibtex`" $ do
        testProgram <- runIO $ parseFromFile "assets/bibtex.pr"
        let infered = fromRight' (inferAndCheckProgram (fromRight' testProgram))
        it "Starts with a program with some BLitEq calls" $ do 
            (hasLitEq infered) `shouldBe` True
        it "Ends with a program without function calls" $ do
            let eliminated = removeBLitEq infered
            (hasLitEq eliminated) `shouldBe` False
        it "The program still works" $ do
            let eliminated = removeBLitEq infered
            let input = "John Doe and Jane and Frank Fabio"
            let expected = runProgramString (untypeProgram infered)    input
            let actual   = runProgramString   (untypeProgram eliminated) input
            actual `shouldBe` expected


