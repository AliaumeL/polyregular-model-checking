module ForLoopExpansionSpec where

import Test.Hspec

import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing
import Parser.ParseHighLevel
import ForPrograms.HighLevel.Interpreter
import ForPrograms.HighLevel.Typing.Inference (inferAndCheckProgram)

import ForPrograms.HighLevel.Transformations.BooleanElimination
import ForPrograms.HighLevel.Transformations.FunctionElimination
import ForPrograms.HighLevel.Transformations.LiteralElimination
import ForPrograms.HighLevel.Transformations.ReductionLitEq
import ForPrograms.HighLevel.Transformations.AddrVarElimination
import ForPrograms.HighLevel.Transformations.LetElimination (eliminateLetProgram)
import ForPrograms.HighLevel.Transformations.ReturnElimination (retElimProgram)
import ForPrograms.HighLevel.Transformations.ForLoopExpansion

import Control.Monad


fromRight' :: Either a b -> b
fromRight' (Right x) = x
fromRight' _ = error "fromRight'"


testProgramAgainst :: [String] -> Program String () -> (String -> String) -> Spec
testProgramAgainst inputs program handCrafted = do
    forM_ inputs $ \input -> do
        it ("works for «" ++ input ++ "»") $ do
            let expected = handCrafted input
            let actual = runProgramString program input
            actual `shouldBe` (Right expected)

testProgramOn :: [(String, String)] -> Program String () -> Spec
testProgramOn inputs program = do
    forM_ inputs $ \(input, expected) -> do
        it ("works for «" ++ input ++ "»") $ do
            let actual = runProgramString program input
            actual `shouldBe` (Right expected)

getProgram :: String -> IO (Program String ValueType)
getProgram file = do 
    testProgram <- parseFromFile file
    let typedProgram = fromRight' . inferAndCheckProgram $ fromRight' testProgram
    let noLitEq     = removeBLitEq typedProgram
    let noFunctions = eliminateFunctionCalls noLitEq
    let noBools     = removeBooleanGen noFunctions
    let noLiterals  = eliminateLiterals noBools
    let noLetOutput = eliminateLetProgram noLiterals
    let noReturn    = retElimProgram noLetOutput
    return noReturn
    
transformProgram :: Program String ValueType -> Program String ()
transformProgram p = case forLoopExpansion p of 
    Right p' -> fmap (const ())  p'
    Left e -> error $ show e


spec :: Spec
spec = do
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/HighLevel/identity.pr"
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           (\x -> x) 
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/HighLevel/reverse.pr"
        let newProgClassicalVars = transformProgram p
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           reverse
    describe "We correctly compute `bibtex`" $ do
        testProgram <- runIO $ getProgram "assets/HighLevel/bibtex.pr"
        testProgramOn [("John", "John"), ("", ""), ("John Doe", "Doe, John"), ("John and Jane Doe", "John and Doe, Jane"), ("John F. Kennedy", "Kennedy, John F.")]
                      (transformProgram testProgram)
    {- 
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/map_reverse.pr"
        let newProgClassicalVars = transformProgram p
         ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           (\x -> x) 
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/bibtex.pr"
        let newProgClassicalVars = transformProgram p
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           (\x -> x) 
    -}
