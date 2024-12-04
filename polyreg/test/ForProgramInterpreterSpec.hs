module ForProgramInterpreterSpec where


import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import Parser.ParseHighLevel

reverseOrderOfWords :: String -> String
reverseOrderOfWords = unwords . reverse . words

fromRight' :: Either a b -> b
fromRight' (Right x) = x
fromRight' _ = error "fromRight'"

spec :: Spec
spec = do
    testProgram <- runIO $ parseFromFile "assets/word_split.pr"
    let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
    describe "We correctly compute reverseOrderOfWords" $ do
        it "works for «go to park»" $ do
            let input = "go to park"
            let expected = reverseOrderOfWords input
            let actual = runProgramString untypedTestProgram input
            actual `shouldBe` (Right expected)
        it "works for «»" $ do
            let input = ""
            let expected = reverseOrderOfWords input
            let actual = runProgramString untypedTestProgram input
            actual `shouldBe` (Right expected)
        it "works for «one_word»" $ do
            let input = "one_word"
            let expected = reverseOrderOfWords input
            let actual = runProgramString untypedTestProgram input
            actual `shouldBe` (Right expected)
        it "works for «a  b»" $ do
            let input = "a  b"
            let expected = reverseOrderOfWords input
            let actual = runProgramString untypedTestProgram input
            actual `shouldBe` (Right expected)
        it "works for «       »" $ do
            let input = "       "
            let expected = reverseOrderOfWords input
            let actual = runProgramString untypedTestProgram input
            actual `shouldBe` (Right expected)
