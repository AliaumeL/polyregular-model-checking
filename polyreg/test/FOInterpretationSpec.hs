module FOInterpretationSpec where

import Test.Hspec
import Test.QuickCheck

import FOInterpretation
import QuantifierFree

type Var  = String
type Alph = Char
type Tag  = String


-- (exists x. 
--     forall y <= x. a(y)
--     /\
--     forall y > x.  b(y))
-- OR
-- (forall x. b(x)) 
formulaAstarBstar = FOBin Disj allBs asThenBs
    where 
        allBs = FOQuant Forall "x" (FOCharAt "x" 'b')
        leqThenA = FOBin Impl (FOTestPos Le "y" "x") (FOCharAt "y" 'a')
        gtThenB  = FOBin Impl (FOTestPos Gt "y" "x") (FOCharAt "y" 'b')
        asThenBs = FOQuant Exists "x" $ 
                        FOQuant Forall "y" $ 
                            FOBin Conj gtThenB leqThenA

aStarBStar :: String -> Bool 
aStarBStar = (== "") . dropWhile (== 'b') . dropWhile (== 'a') 

-- | First FO interpretation: identity function
identityFOI :: FOInterpretation Var Alph Tag 
identityFOI = Interpretation tags outputLetters domainFormula orderFormula labelFormula copyFormula arity maxArity
    where
        tags = ["t"]
        outputLetters = []
        domainFormula _ _ = FOTrue
        orderFormula _ _ (x : _) (y : _) = FOTestPos Le x y
        orderFormula _ _ _ _ = error "Invalid position tuples"
        labelFormula _ _ _ = FOFalse
        copyFormula  _ _ _ = FOTrue
        arity _ = 1
        maxArity = 1

-- | Second FO interpretation: reverse function
reverseFOI :: FOInterpretation Var Alph Tag 
reverseFOI = Interpretation tags outputLetters domainFormula orderFormula labelFormula copyFormula arity maxArity
    where
        tags = ["t"]
        outputLetters = []
        domainFormula _ _ = FOTrue
        orderFormula _ _ (x : _) (y : _) = FOTestPos Ge x y
        orderFormula _ _ _ _ = error "Invalid position tuples"
        labelFormula _ _ _ = FOFalse
        copyFormula  _ _ _ = FOTrue
        arity _ = 1
        maxArity = 1

-- | Third FO interpretation: duplicate function
duplicateFOI :: FOInterpretation Var Alph Tag 
duplicateFOI = Interpretation tags outputLetters domainFormula orderFormula labelFormula copyFormula arity maxArity
    where
        tags = ["A", "B"]
        outputLetters = []
        domainFormula _ _ = FOTrue
        orderFormula "A" "A" (x : _) (y : _) = FOTestPos Le x y
        orderFormula "A" "B" (x : _) (y : _) = FOTrue
        orderFormula "B" "A" (x : _) (y : _) = FOFalse
        orderFormula "B" "B" (x : _) (y : _) = FOTestPos Le x y
        orderFormula _ _ _ _ = error "Invalid position tuples"
        labelFormula _ _ _ = FOFalse
        copyFormula  _ _ _ = FOTrue
        arity _ = 1
        maxArity = 1

lexFormula :: [Var] -> [Var] -> Formula Var Alph
lexFormula [] [] = error "lexicographic ordering needs at least one position"
lexFormula [x] [y] = FOTestPos Le x y
lexFormula (x : xs) (y : ys) = FOBin Disj lt (FOBin Conj eq rest)
    where
        eq = FOTestPos Eq x y 
        lt = FOTestPos Lt x y
        rest = lexFormula xs ys

-- | Fourth FO interpretation: squaring
squaringFOI :: FOInterpretation Var Alph Tag
squaringFOI = Interpretation tags outputLetters domainFormula orderFormula labelFormula copyFormula arity maxArity
    where
        tags = ["A"]
        outputLetters = []
        domainFormula _ _ = FOTrue
        orderFormula _ _ xs ys = lexFormula xs ys
        labelFormula _ _ _ = FOFalse
        copyFormula  _ 0 _ = FOFalse
        copyFormula  _ 1 _ = FOTrue
        arity _ = 2
        maxArity = 2

squaring :: String -> String
squaring w = concat . map (\_ -> w) $ w


spec :: Spec
spec = do
    describe "The evaluator for FO Formulas (FOInterpretation.evalFormula)" $ do
        it "Correctly implements false" $ property $
            \x -> (evalFormula FOFalse x) `shouldBe` False
        it "Correctly implements true" $ property $
            \x -> (evalFormula FOTrue x) `shouldBe` True
        it "Correctly implements `there is an a`" $ property $
            \x -> (evalFormula (FOQuant Exists "x" (FOCharAt "x" 'a')) x) `shouldBe` (any (== 'a') x)
        it "Correctly implements `all are a’s`" $ property $
            \x -> (evalFormula (FOQuant Forall "x" (FOCharAt "x" 'a')) x) `shouldBe` (all (== 'a') x)
        it "Correctly recognizes a^* b^*" $ property $
            \x -> (evalFormula formulaAstarBstar x) `shouldBe` aStarBStar x

    describe "The interpreter for simple for FOInterpretations (FOInterpretation.evalInterpretation)" $ do
        it "Correctly computes the identity function" $ property $
            \x -> (evalInterpretation identityFOI x) `shouldBe` (x :: String)
        it "Correctly computes the reverse function" $ property $
            \x -> (evalInterpretation reverseFOI x) `shouldBe` (reverse x)
        it "Correctly computes the reverse function (specific examples)" $ do
            evalInterpretation reverseFOI "aba" `shouldBe` "aba"
            evalInterpretation reverseFOI "abab" `shouldBe` "baba"
            evalInterpretation reverseFOI "aaaabbbb" `shouldBe` "bbbbaaaa"
        it "Correctly computes the duplicate function" $ property $
            \x -> (evalInterpretation duplicateFOI x) `shouldBe` (x ++ x)
        it "Correctly computes the duplicate function (specific examples)" $ do
            evalInterpretation duplicateFOI "a" `shouldBe` "aa"
            evalInterpretation duplicateFOI "ab" `shouldBe` "abab"
            evalInterpretation duplicateFOI "ba" `shouldBe` "baba"
            evalInterpretation duplicateFOI "aba" `shouldBe` "abaaba"
        it "Correctly computes the squaring function" $ property $
            \x -> (evalInterpretation squaringFOI x) `shouldBe` (squaring x)
