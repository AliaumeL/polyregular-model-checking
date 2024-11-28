module HighLevelForProgramsInterpreterSpec where

import Test.Hspec
-- import qualified Test.QuickCheck as Q
-- import Test.QuickCheck (property)

-- import HighLevelForProgramsInterpreter
-- import HighLevelForPrograms

-- import Data.List
-- import Data.List.Split


-- -- identity 
-- -- for (i, v) in w:
-- --  yield (v)

-- identityProgram :: [Function Char]
-- identityProgram = [identityF]
--     where
--         identityF = Function "main" [("w", TVal (TList TChar))] identityS 
--         identityS = StatementBlock [] [For "i" "v" (VVar "w") (StatementBlock [] [Yield (VVar "v")] (TList TChar))] (TList TChar)


-- -- hasB = False
-- -- for (i, v) in w
-- --  if v == "b" then 
-- --      hasB = True
-- --  if hasB then
-- --      yield ("b")
-- --  else
-- --      yield (v)

-- thenBsProgram :: [Function Char]
-- thenBsProgram = [thenBsF]
--     where
--         thenBsF = Function "main" [("w", TVal (TList TChar))] thenBsS 
--         thenBsS = StatementBlock ["hasB"] [For "i" "v" (VVar "w") (StatementBlock [] [thenBsIf, thenBsPrt] (TList TChar))] (TList TChar)
--         thenBsIf = If (BEqVal (VVar "v") (ListLiteral (VChar 'b') TChar) ) [SetTrue "hasB"] []
--         thenBsPrt = If (BVar "hasB") [Yield (ListLiteral (VChar 'b') TChar)] [Yield (VVar "v")]

-- thenBs :: String -> String
-- thenBs [] = []
-- thenBs ('b':xs) = 'b': (map (\_ -> 'b') xs)
-- thenBs (x:xs) = x:thenBs xs

-- --- A function that transforms two ways of displaying lists of latex authors. 
-- --- John Doe -> Doe, John 
-- --- John Doe and Jane Doe -> Doe, John and Doe, Jane
-- --- John F Kennedy -> Kennedy, John F
-- --- Alice and Bob --> Alice and Bob

-- latexTransform :: String -> String 
-- latexTransform w = intercalate " and " $ map f authors 
--   where
--     ws = words w
--     authors = splitOn ["and"] ws 
--     f [] = [] 
--     f [x] = x 
--     f xs = last xs  ++ ", " ++  unwords (init xs)

-- wordsF :: Function Char 
-- wordsF = Function "words" [("w", TVal (TList TChar))] wordsS
--     where
--         wordsS = StatementBlock [] [yieldFirstWord, For "i" "v" (VVar "w") (StatementBlock [] [yieldWordIfSpace] (TList TChar))] (TList TChar)
--         yieldFirstWord = Yield (VFunctionCall "getFirstWord" [ValExpr $ VVar "w"])
--         yieldWordIfSpace = If (BEqVal (VVar "v") (ListLiteral (VChar ' ') TChar) ) [Yield (VFunctionCall "getWord" [ValExpr $ VVar "w", PosExpr "i"])] []
    
-- getFirstWord :: Function Char
-- getFirstWord = Function "getFirstWord" [("w", TVal (TList TChar))] getFirstWordS
--     where
--         getFirstWordS = StatementBlock ["after_space"] [For "j" "v" (VVar "w") (StatementBlock [] [update, condPrint] (TList TChar))] (TList TChar)
--         update = If (BEqVal (VVar "v") (ListLiteral (VChar ' ') TChar) ) [SetTrue "after_space"] []
--         condPrint = If (BVar "after_space") [] [Yield (VVar "v")]
        

-- getWord :: Function Char
-- getWord = Function "getWord" [("w", TVal (TList TChar)), ("i", TPos (VVar "w"))] getWordS
--     where
--         getWordS = StatementBlock ["after_space"] [For "j" "v" (VVar "w") (StatementBlock [] [bigIf] (TList TChar))] (TList TChar)
--         bigIf = If (BPosBinOp PosGt "j" "i") [getWordIf, getWordPrt] []
--         getWordIf = If (BEqVal (VVar "v") (ListLiteral (VChar ' ') TChar) ) [SetTrue "after_space"] []
--         getWordPrt = If (BVar "after_space") [] [Yield (VVar "v")]

-- andParts :: Function Char 
-- andParts = Function "andParts" [("w", TVal (TList $ TList TChar))] wordsS
--     where
--         wordsS = StatementBlock [] [yieldFirstWord, For "i" "v" (VVar "w") (StatementBlock [] [yieldWordIfSpace] (TList $ TList TChar))] (TList $ TList TChar)
--         yieldFirstWord = Yield (VFunctionCall "getFirstAndPart" [ValExpr $ VVar "w"])
--         yieldWordIfSpace = If (BEqVal (VVar "v") (ListLiteral (VList (VChar <$> "and")) (TList TChar)) ) [Yield (VFunctionCall "getAndPart" [ValExpr $ VVar "w", PosExpr "i"])] []
    
-- getFirstAndPart :: Function Char
-- getFirstAndPart = Function "getFistAndPart" [("w", TVal (TList $ TList TChar))] getFirstWordS
--     where
--         getFirstWordS = StatementBlock ["after_space"] [For "j" "v" (VVar "w") (StatementBlock [] [update, condPrint] (TList $ TList TChar))] (TList $ TList TChar)
--         update = If (BEqVal (VVar "v") (ListLiteral (VList (VChar <$> "and")) (TList TChar) )) [SetTrue "after_space"] []
--         condPrint = If (BVar "after_space") [] [Yield (VVar "v")]
        
-- getAndPart :: Function Char
-- getAndPart = Function "getAndPart" [("w", TVal (TList TChar)), ("i", TPos (VVar "w"))] getWordS
--     where
--         getWordS = StatementBlock ["after_space"] [For "j" "v" (VVar "w") (StatementBlock [] [bigIf] (TList $ TList TChar))] (TList $ TList TChar)
--         bigIf = If (BPosBinOp PosGt "j" "i") [getWordIf, getWordPrt] []
--         getWordIf = If (BEqVal (VVar "v") (ListLiteral (VList (VChar <$> "and")) (TList TChar))) [SetTrue "after_space"] []
--         getWordPrt = If (BVar "after_space") [] [Yield (VVar "v")]

-- getFirst :: Function Char 
-- getFirst = Function "getFirst" [("w", TVal (TList TChar))] getFirstS
--     where
--         getFirstS = StatementBlock ["after_first"] [For "j" "v" (VVar "w") (StatementBlock [] [condPrint, update] (TList TChar))] (TList TChar)
--         condPrint = If (BVar "after_fist") [] [Yield (VVar "v")]
--         update = SetTrue "after_first"

-- -- Now, we combine reverse and get First to get getLast
-- getLast :: Function Char
-- getLast = Function "getLast" [("w", TVal (TList TChar))] getLastS
--     where
--         getLastS = StatementBlock [] [lopAndYield] (TList TChar)
--         lopAndYield = For "j" "v"  (VFunctionCall "getFirst" [ValExpr $ VRev (VVar "w")]) (StatementBlock [] [Yield (VVar "v")] (TList TChar))

-- dropFirst :: Function Char
-- dropFirst = Function "dropFirst" [("w", TVal (TList TChar))] getFirstS
--     where
--         getFirstS = StatementBlock ["after_first"] [For "j" "v" (VVar "w") (StatementBlock [] [condPrint, update] (TList TChar))] (TList TChar)
--         condPrint = If (BVar "after_fist") [Yield (VVar "v")] [] 
--         update = SetTrue "after_first"

-- dropLast :: Function Char
-- dropLast = Function "dropLast" [("w", TVal (TList TChar))] getLastS
--     where
--         getLastS = StatementBlock [] [lopAndYield] (TList TChar)
--         lopAndYield = For "j" "v"  (VRev $ VFunctionCall "dropFirst" [ValExpr $ VRev (VVar "w")]) (StatementBlock [] [Yield (VVar "v")] (TList TChar))

-- intercalateF :: Function Char
-- intercalateF = Function "intercalate" [("w", TVal (TList TChar)), ("sep", TVal TChar)] intercalateS
--     where
--         intercalateS = StatementBlock ["first"] [For "j" "v" (VVar "w") (StatementBlock [] [condPrint, update] (TList TChar))] (TList TChar)
--         condPrint = If (BVar "first") [produceV] [produceSep, produceV]
--         produceV = For "k" "u" (VVar "v") (StatementBlock [] [Yield (VVar "u")] (TList TChar))
--         produceSep = For "k" "u" (VVar "sep") (StatementBlock [] [Yield (VVar "u")] (TList TChar))
--         update = SetTrue "first"

-- concatF :: Function Char 
-- concatF = Function "concat" [ ("u", TVal $ TList $ TList Char)] (StatementBlock [] [nestedFor] (TListChar)) 

-- prepareAuthors :: Function Char
-- prepareAuthors = Function "prepareAuthors" [("w", TVal (TList $ TList TChar))] prepareAuthorsS
--     where
--         prepareAuthorsS = StatementBlock [] [For "j" "author" (VVar "w") (StatementBlock [] [prepareAuthor] (TList TChar))] (TList TChar)
--         prepareAuthor = undefined


-- spec :: Spec
-- spec = do
--     describe "The evaluator works for the identity function" $ do
--         it "Correctly computes the identity function (random tests)" $ property $
--             \x -> (runForProgram identityProgram x `shouldBe` (Right . VList $  map VChar x))
--         it "Correctly computes the identity function (specific example)" $ do
--             (runForProgram identityProgram "abc") `shouldBe` (Right . VList $  map VChar "abc")
--             (runForProgram identityProgram "abc") `shouldBe` (Right . VList $  map VChar "abc")
--     describe "The evaluator works for the thenBs function" $ do
--         it "Correctly computes the identity function (random tests)" $ property $
--             \x -> (runForProgram thenBsProgram x `shouldBe` (Right . VList . map VChar . thenBs $ x))
--         it "Correctly computes the identity function (specific example)" $ do
--             (runForProgram thenBsProgram "aaaabaaa") `shouldBe` (Right . VList $  map VChar "aaaabbbb")
--             (runForProgram thenBsProgram "aaacaaa") `shouldBe` (Right . VList $  map VChar "aaacaaa")
--     describe "Our Haskell implementation of latexTransform works" $ do
--         it "Works correctly on 'John Doe' " $ do
--             latexTransform "John Doe" `shouldBe` "Doe, John"
--         it "Works correctly on 'John Doe and Jane Doe' " $ do
--             latexTransform "John Doe and Jane Doe" `shouldBe` "Doe, John and Doe, Jane"
--         it "Works correctly on 'John F Kennedy' " $ do
--             latexTransform "John F Kennedy" `shouldBe` "Kennedy, John F"
--         it "Works correctly on 'Alice and Bob' " $ do
--             latexTransform "Alice and Bob" `shouldBe` "Alice and Bob"

spec :: Spec
spec = return ()

