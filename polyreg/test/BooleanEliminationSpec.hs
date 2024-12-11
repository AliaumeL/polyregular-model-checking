module BooleanEliminationSpec where

import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import ForProgramsTyping
import Parser.ParseHighLevel
import Typing.Inference (inferAndCheckProgram)
import FunctionElimination (eliminateFunctionCalls)
import BooleanElimination (hasBooleanGen, removeBooleanGen)

fromRight' :: (Show b, Show a) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight': " ++ show e

untypeProgram :: Program String a -> Program String ()
untypeProgram = fmap (const ())

spec :: Spec
spec = do 
    testProgram <- runIO $ parseFromFile "assets/boolean_funcs.pr"
    let infered = fromRight' (inferAndCheckProgram (fromRight' testProgram))
    let elim    = eliminateFunctionCalls infered
    describe "We actually remove boolean generators" $ do
        it "Starts with a program with some generators calls" $ do 
            (hasBooleanGen elim) `shouldBe` True
        it "Ends with a program without generators" $ do
            let genFree = removeBooleanGen elim
            (hasBooleanGen genFree) `shouldBe` False
        it "The program still works" $ do
            let genFree = removeBooleanGen elim
            let input = "go to park"
            let expected = runProgramString (untypeProgram elim)    input
            let actual   = runProgramString (untypeProgram genFree) input
            actual `shouldBe` expected
