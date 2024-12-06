module ForProgramInterpreterSpec where


import Test.Hspec

import ForPrograms
import ForProgramInterpreter
import Parser.ParseHighLevel


import Control.Monad

dumbWords :: String -> [String]
dumbWords w = go w []
    where
        go :: String -> String -> [String]
        go [] acc = [reverse acc]
        go (' ' : xs) acc = (reverse acc) : go xs []
        go (x : xs) acc = go xs (x : acc)

dumbUnWords :: [String] -> String
dumbUnWords [] = ""
dumbUnWords [x] = x
dumbUnWords (x:xs) = x ++ " " ++ dumbUnWords xs

reverseOrderOfWords :: String -> String
reverseOrderOfWords = dumbUnWords . reverse . dumbWords

fromRight' :: (Show a, Show b) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error $ "fromRight'" ++ show e

testProgramAgainst :: [String] -> Program String () -> (String -> String) -> Spec
testProgramAgainst inputs program handCrafted = do
    forM_ inputs $ \input -> do
        it ("works for «" ++ input ++ "»") $ do
            let expected = handCrafted input
            let actual = runProgramString program input
            actual `shouldBe` (Right expected)


testProgramOn :: [(String, String)] -> Program String () -> Spec
testProgramOn inputs program = do
    forM_ inputs $ \(input, expected) -> do
        it ("works for «" ++ input ++ "»") $ do
            let actual = runProgramString program input
            actual `shouldBe` (Right expected)


spec :: Spec
spec = do
    describe "We correctly compute reverseOrderOfWords" $ do
        testProgram <- runIO $ parseFromFile "assets/word_split.pr"
        let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
        testProgramAgainst ["go to park", "", "one_word", "a  b", "       "] 
                           untypedTestProgram
                           reverseOrderOfWords
    describe "We correctly compute `bibtex`" $ do
        testProgram <- runIO $ parseFromFile "assets/bibtex.pr"
        let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
        testProgramOn [("John", "John"), ("", ""), ("John Doe", "Doe, John"), ("John and Jane Doe", "John and Doe, Jane"), ("John F. Kennedy", "Kennedy, John F.")]
                      untypedTestProgram
    describe "We correctly compute `reverse`" $ do
        testProgram <- runIO $ parseFromFile "assets/reverse.pr"
        let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
        testProgramAgainst ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
                      untypedTestProgram
                      reverse
    describe "We correctly compute `identity`" $ do
        testProgram <- runIO $ parseFromFile "assets/identity.pr"
        let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
        testProgramAgainst ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
                      untypedTestProgram
                      (\x -> x)
    describe "We correctly compute `map reverse`" $ do
        testProgram <- runIO $ parseFromFile "assets/map_reverse.pr"
        let untypedTestProgram = fmap (const ()) $ fromRight' testProgram
        testProgramAgainst ["a", "", "a b", "ab abc", "abcd a a abcd", "abc def ghi"]
                      untypedTestProgram
                      (dumbUnWords . map reverse . dumbWords)
                      
                       


