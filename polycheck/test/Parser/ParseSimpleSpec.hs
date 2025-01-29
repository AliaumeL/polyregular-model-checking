module Parser.ParseSimpleSpec where 

import Test.Hspec
import Parser.ParseSimple
import Data.Either

import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM_)

testProgramString :: IO String
testProgramString = readFile "assets/SimpleForPrograms/reverse_if_contains_a.spr"

spec :: Spec
spec = do 
    testProgram <- runIO testProgramString
    describe "The parser should be able to parse programs" $ do
        -- check if the parser can parse all programs from assets/SimpleForPrograms"
        -- first we list all the files in the directory
        allFiles <- runIO $ listDirectory "assets/SimpleForPrograms"
        let files = filter (\f -> takeExtension f == ".spr") allFiles
        forM_ files $ \file -> do
            it ("Parses the program " ++ file) $ do
                program <- readFile ("assets/SimpleForPrograms" </> file)
                let parsed = parseSimpleForProgram program
                parsed `shouldSatisfy` isRight
        it "Parses a simple program" $ do
            let parsed = parseSimpleForProgram testProgram
            parsed `shouldSatisfy` isRight