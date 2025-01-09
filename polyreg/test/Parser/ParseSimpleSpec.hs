module Parser.ParseSimpleSpec where 

import Test.Hspec
import Parser.ParseSimple
import Data.Either

testProgramString :: IO String
testProgramString = readFile "assets/SimpleForPrograms/reverse_if_contains_a.spr"

spec :: Spec
spec = do 
    testProgram <- runIO testProgramString
    describe "The parser should be able to parse programs" $ do 
        it "Parses a simple program" $ do
            let parsed = parseSimpleForProgram testProgram
            parsed `shouldSatisfy` isRight