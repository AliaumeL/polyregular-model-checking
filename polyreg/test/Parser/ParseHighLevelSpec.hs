module Parser.ParseHighLevelSpec where

import Test.Hspec
import Parser.ParseHighLevel
import Data.Either


testProgramString :: IO String
testProgramString = readFile "assets/word_split.pr"

spec :: Spec
spec = do 
    testProgram <- runIO testProgramString
    describe "The parser should be able to parse programs" $ do 
        it "Parses a simple program" $ do
            let parsed = parseHighLevel testProgram
            parsed `shouldSatisfy` isRight
