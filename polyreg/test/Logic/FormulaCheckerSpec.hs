module Logic.FormulaCheckerSpec where

import Test.Hspec

import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension)
import Parser.ParseFirstOrder (parseFromFile)
import Logic.FormulaChecker (checkFormulaTypes, TypeError(..))

import Data.Map (Map)
import qualified Data.Map as M

import Data.Either (isRight, isLeft)
import Control.Monad (forM_)

import Logic.QuantifierFree
import Logic.Formulas

-- This formula tries to compare a Boolean variable with a Tag variable
invalidFormula1 :: Formula ()
invalidFormula1 = FBin Conj (FBin Equiv (FVar (In "boolVar")) (FVar (In "tagVar"))) (FTag (In "tagVar") ())

-- This formula tries to perform a position test on a Boolean variable
invalidFormula2 :: Formula () 
invalidFormula2 = FBin Conj (FTestPos Le (In "boolVar") (In "posVar")) (FVar (In "boolVar"))

-- This formula tries to use a local variable that is not in scope
invalidFormula3 :: Formula ()
invalidFormula3 = FVar (Local 2 "localVar")

-- This formula uses a quantifier with an incorrect sort
invalidFormula4 :: Formula ()
invalidFormula4 = FQuant Exists "boolVar" Boolean (FTag (Local 0 "boolVar") ())

-- This formula uses a binary operation with inconsistent types
invalidFormula5 :: Formula () 
invalidFormula5 = FBin Conj (FVar (In "boolVar")) (FLetter (In "boolVar") 'a')

checkFile :: FilePath -> IO (Either TypeError (Map Var Sort))
checkFile file = do
  result <- parseFromFile ("assets/Formulas" </> file)
  case result of
    Left err -> error $ show err
    Right formula -> return $ checkFormulaTypes formula


spec :: Spec
spec = do 
    it "Correctly detects anomalies" $ do
        forM_ [invalidFormula1, invalidFormula2, invalidFormula3, invalidFormula4, invalidFormula5] $ \formula -> do
            checkFormulaTypes formula `shouldSatisfy` isLeft
    it "typechecks formulas from assets/Formulas" $ do
      files <- listDirectory "assets/Formulas"
      let formulaFiles = filter (\f -> takeExtension f == ".fo") files
      -- check that everyone returns a Right
      -- and that the resulting map is empty!
      forM_ formulaFiles $ \file -> do
        result <- checkFile file
        result `shouldSatisfy` isRight
        let Right m = result
        m `shouldBe` M.empty
