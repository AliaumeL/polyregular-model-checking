module Parser.ParseHighLevelSpec where

import Test.Hspec
import Parser.ParseHighLevel
import Data.Either


testProgramString :: IO String
testProgramString = readFile "assets/HighLevel/bibtex.pr"

spec :: Spec
spec = do 
    testProgram <- runIO testProgramString
    describe "The parser should be able to parse programs" $ do 
        it "Parses the bibtex program" $ do
            let parsed = parseHighLevel testProgram
            parsed `shouldSatisfy` isRight
