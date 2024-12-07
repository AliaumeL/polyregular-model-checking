module GraphTypeInferenceSpec where

import Test.Hspec

import Control.Monad

import qualified Typing.Constraints as C
import qualified Typing.Inference as I

import ForPrograms
import ForProgramsTyping
import ForProgramInterpreter
import Parser.ParseHighLevel

import Debug.Trace

-- traverse to list
import Data.Foldable (toList)

fromRight' :: (Show a, Show b) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight'" ++ show e

getProgram :: String -> IO (Program String (Maybe ValueType))
getProgram path = do
    program <- parseFromFile path
    return $ fromRight' program

-- forgets positions and remaps types to be able to compare
forgetPositionType :: ValueType -> Maybe ValueType
forgetPositionType (TOutput t) = Just (TOutput t)
forgetPositionType (TBool) = Just TBool
forgetPositionType (TConst t) = Just (TOutput t)
forgetPositionType _ = Nothing


typeProgramBothWays program = case (classicalInference, newInference) of
                                (Right p1, Right p2) -> do 
                                    (fmap forgetPositionType p1) `shouldBe` p2
                                (_, Left e) -> error $ "Failed to type program" ++ show e
                                (Left e, _) -> error $ "Failed to type program" ++ show e
    where
        classicalInference = inferProgram program
        newInference = I.inferTypes program

spec :: Spec
spec = do
    describe "We can infer types for usual programs" $ do
        forM_ ["assets/word_split.pr", "assets/boolean_funcs.pr", "assets/bibtex.pr", "assets/identity.pr", "assets/reverse.pr", "assets/map_reverse.pr"] $ \path -> do
            program <- runIO (getProgram path)
            it ("works for «" ++ path ++ "»") $ do
                typeProgramBothWays program
