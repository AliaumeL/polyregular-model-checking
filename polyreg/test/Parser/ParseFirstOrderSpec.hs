module Parser.ParseFirstOrderSpec where

import Test.Hspec
import Control.Monad

import Parser.ParseFirstOrder
import Logic.Formulas
import Logic.QuantifierFree
import System.Directory 


isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

readAllAssetsFormulas :: IO [(String, String)]
readAllAssetsFormulas = do
    -- We read all files from the assets folder
    let dir = "assets/Formulas/"
    files <- listDirectory dir
    let fullPaths = map (dir ++) files
    forM fullPaths (\path -> do
        content <- readFile path
        return (drop (length dir) path, content))



containsABString :: IO String 
containsABString = readFile "assets/Formulas/containsAB.fo"

containsABFormula :: Formula String
containsABFormula = FQuant Exists "firstC" Pos (FQuant Exists "nextC" Pos (FBin Conj (FTestPos Lt (Local 1 "firstC") (Local 0 "nextC")) (FBin Conj (FNot (FQuant Exists "middleLetter" Pos (FBin Conj (FTestPos Lt (Local 2 "firstC") (Local 0 "middleLetter")) (FTestPos Lt (Local 0 "middleLetter") (Local 1 "nextC"))))) (FBin Conj (FLetter (Local 1 "firstC") 'a') (FLetter (Local 0 "nextC") 'b')))))

spec :: Spec
spec = do 
    describe "The parser should be able to parse first order formulas" $ do 
        formula <- runIO containsABString
        it "Parses a simple first order formula" $ do
            let parsed = parseFirstOrderFormula formula
            parsed `shouldBe` (Right containsABFormula)
    describe "The parser should parse all formulas in Assets/Formulas " $ do
        files <- runIO readAllAssetsFormulas
        forM_ files (\(name, content) -> do
            it ("Parses the formula " ++ name) $ do
                let parsed = parseFirstOrderFormula content
                parsed `shouldSatisfy` isRight
            )

    