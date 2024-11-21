module HighLevelForProgramsInterpreterSpec where

import Test.Hspec
import qualified Test.QuickCheck as Q
import Test.QuickCheck (property)

import HighLevelForProgramsInterpreter
import HighLevelForPrograms


-- identity 
-- for (i, v) in w:
--  yield (v)

identityProgram :: [Function Char]
identityProgram = [identityF]
    where
        identityF = Function "main" [("w", TVal (TList TChar))] identityS 
        identityS = StatementBlock [] [For "i" "v" (VVar "w") (StatementBlock [] [Yield (VVar "v")] (TList TChar))] (TList TChar)


-- hasB = False
-- for (i, v) in w
--  if v == "b" then 
--      hasB = True
--  if hasB then
--      yield ("b")
--  else
--      yield (v)

thenBsProgram :: [Function Char]
thenBsProgram = [thenBsF]
    where
        thenBsF = Function "main" [("w", TVal (TList TChar))] thenBsS 
        thenBsS = StatementBlock ["hasB"] [For "i" "v" (VVar "w") (StatementBlock [] [thenBsIf, thenBsPrt] (TList TChar))] (TList TChar)
        thenBsIf = If (BEqVal (VVar "v") (ListLiteral (VChar 'b') TChar) ) [SetTrue "hasB"] []
        thenBsPrt = If (BVar "hasB") [Yield (ListLiteral (VChar 'b') TChar)] [Yield (VVar "v")]

thenBs :: String -> String
thenBs [] = []
thenBs ('b':xs) = 'b': (map (\_ -> 'b') xs)
thenBs (x:xs) = x:thenBs xs


spec :: Spec
spec = do
    describe "The evaluator works for the identity function" $ do
        it "Correctly computes the identity function (random tests)" $ property $
            \x -> (runForProgram identityProgram x `shouldBe` (Right . VList $  map VChar x))
        it "Correctly computes the identity function (specific example)" $ do
            (runForProgram identityProgram "abc") `shouldBe` (Right . VList $  map VChar "abc")
            (runForProgram identityProgram "abc") `shouldBe` (Right . VList $  map VChar "abc")
    describe "The evaluator works for the thenBs function" $ do
        it "Correctly computes the identity function (random tests)" $ property $
            \x -> (runForProgram thenBsProgram x `shouldBe` (Right . VList . map VChar . thenBs $ x))
        it "Correctly computes the identity function (specific example)" $ do
            (runForProgram thenBsProgram "aaaabaaa") `shouldBe` (Right . VList $  map VChar "aaaabbbb")
            (runForProgram thenBsProgram "aaacaaa") `shouldBe` (Right . VList $  map VChar "aaacaaa")

