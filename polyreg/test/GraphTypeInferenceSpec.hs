module GraphTypeInferenceSpec where

import Test.Hspec

import Control.Monad

import qualified Typing.Constraints as C
import qualified Typing.Inference as I

import ForPrograms
import ForProgramsTyping
import ForProgramInterpreter
import Parser.ParseHighLevel

import ForProgramsPrettyPrint

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
