module ForProgramTypingSpec where

import Data.Either

import Test.Hspec

import ForProgramsTyping
import ForPrograms
import Parser.ParseHighLevel


fromRight' :: Either a b -> b
fromRight' (Right x) = x
fromRight' _ = error "fromRight'"

spec :: Spec
spec = do
    testProgram <- runIO $ parseFromFile "assets/word_split.pr"
    describe "The type inference does not fail" $ do
        let infered = inferProgram (fromRight' testProgram)
        it "Infered program" $ do
            infered `shouldSatisfy` isRight
