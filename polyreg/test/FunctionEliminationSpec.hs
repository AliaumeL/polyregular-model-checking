module FunctionEliminationSpec where

import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import ForProgramsTyping
import Parser.ParseHighLevel
import FunctionElimination

fromRight' :: Either a b -> b
fromRight' (Right x) = x
fromRight' _ = error "fromRight'"


untypeProgram :: Program String a -> Program String ()
untypeProgram = fmap (const ())

spec :: Spec
spec = do 
    testProgram <- runIO $ parseFromFile "assets/word_split.pr"
    let infered = fromRight' (inferProgram (fromRight' testProgram))
    describe "We actually remove function calls" $ do
        it "Starts with a program with function calls" $ do 
            (hasFunctionCall infered) `shouldBe` True
        it "Ends with a program without function calls" $ do
            let eliminated = eliminateFunctionCalls infered
            (hasFunctionCall eliminated) `shouldBe` False
        it "The program still works" $ do
            let eliminated = eliminateFunctionCalls infered
            let input = "go to park"
            let expected = runProgramString (untypeProgram infered)    input
            let actual = runProgramString   (untypeProgram eliminated) input
            actual `shouldBe` expected


