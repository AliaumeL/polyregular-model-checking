module Parser.ParseHighLevelSpec where

import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension)

import Data.Either (isRight, isLeft)
import Control.Monad (forM_)

import Test.Hspec
import Parser.ParseHighLevel
import Data.Either

spec :: Spec
spec = do 
    allFiles <- runIO $ listDirectory "assets/HighLevel"
    describe "The parser should be able to parse programs in assets/HighLevel" $ do 
        let files = filter (\f -> takeExtension f == ".pr") allFiles
        forM_ files $ \file -> do
            it ("Parses the program " ++ file) $ do
                program <- readFile ("assets/HighLevel" </> file)
                let parsed = parseHighLevel program
                parsed `shouldSatisfy` isRight
