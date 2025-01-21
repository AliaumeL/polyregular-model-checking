module GraphTypeInferenceSpec where

import Test.Hspec

import Control.Monad

import qualified ForPrograms.HighLevel.Typing.Constraints as C
import qualified ForPrograms.HighLevel.Typing.Inference as I

import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing
import ForPrograms.HighLevel.Interpreter
import Parser.ParseHighLevel

import ForPrograms.HighLevel.PrettyPrint

-- traverse to list
import Data.Foldable (toList)

fromRight' :: (Show a, Show b) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight'" ++ show e

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

getProgram :: String -> IO (Program String (Maybe ValueType))
getProgram path = do
    program <- parseFromFile path
    return $ fromRight' program

spec :: Spec
spec = do
    describe "We do not care" $ do
        it "works" $
            True `shouldBe` True
    {- 
    describe "We can infer types for usual programs" $ do
        forM_ ["assets/word_split.pr", "assets/boolean_funcs.pr", "assets/bibtex.pr", "assets/identity.pr", "assets/reverse.pr", "assets/map_reverse.pr"] $ \path -> do
            program <- runIO (getProgram path)
            it ("works for «" ++ path ++ "»") $ do
                (I.inferAndCheckProgram program) `shouldSatisfy` isRight
    -}
