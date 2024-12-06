module ForLoopExpansionSpec where

import Test.Hspec

import ForPrograms
import ForProgramsTyping
import Parser.ParseHighLevel
import ForProgramInterpreter

import BooleanElimination
import FunctionElimination
import LiteralElimination
import ReductionLitEq
import ForLoopExpansion

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
    let typedProgram = fromRight' . inferProgram $ fromRight' testProgram
    let noLitEq = removeBLitEq typedProgram
    let noFunctions = eliminateFunctionCalls typedProgram
    let noBools     = removeBooleanGen noFunctions
    let noLiterals  = eliminateLiterals noBools
    return noLiterals
    
transformProgram :: Program String ValueType -> Program String ()
transformProgram (Program funcs main) = newProgClassicalVars
    where
        (StmtFun v args body t) = last funcs
        noGenerators = expandGenStmt (mapVars OldVar body)
        newArgs = map (\(n, t, ps) -> (OldVar n, t, map OldVar ps)) args
        newName = OldVar v
        newProg = Program [StmtFun newName newArgs noGenerators t] newName
        newProgUntyped = fmap (const ()) newProg
        newProgClassicalVars = mapVarsProgram (\(OldVar v) -> v) newProgUntyped


spec :: Spec
spec = do
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/identity.pr"
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           (\x -> x) 
    describe "We correctly expand loops" $ do
        p <- runIO $ getProgram "assets/reverse.pr"
        let newProgClassicalVars = transformProgram p
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           (transformProgram p)
                           reverse
    describe "We correctly compute `bibtex`" $ do
        testProgram <- runIO $ getProgram "assets/bibtex.pr"
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
