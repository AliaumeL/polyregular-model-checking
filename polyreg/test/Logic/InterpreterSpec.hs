{-# LANGUAGE RecordWildCards #-}
module Logic.InterpreterSpec where 

import Logic.Interpretation
import Logic.Interpreter
import QuantifierFree
import Logic.Formulas

import Test.Hspec

-- We model the transduction abc -> x a abc b bc c c
squareInterpretation :: Interpretation String
squareInterpretation = Interpretation { .. }
  where 
    tags = ["First", "Initial", "Suffix"]
    alphabet = "abcxis"
    domain "First" [] = FConst True
    domain "Initial" [_] = FConst True
    domain "Suffix" [x, y] = FTestPos Le x y
    order "First" _ _ _ = FConst True
    order "Initial" "Initial" [x] [y] = FTestPos Le x y
    order "Initial" "Suffix"  [x] [y, z] = FTestPos Le x y
    order "Initial" "First" [x] [] = FConst False
    order "Suffix" "Suffix" [x1, y1] [x2, y2] = FBin Disj (FTestPos Lt x1 x2) (FBin Conj (FTestPos Eq x1 x2) (FTestPos Le y1 y2))
    order "Suffix" "Initial" [x, y] [z] = FTestPos Lt x z
    order "Suffix" "First" [x, y] [] = FConst False
    labelOrCopy "First" = Left 'x'
    labelOrCopy "Initial" = Right 0
    labelOrCopy "Suffix" = Right 0
    arity "First" = 0
    arity "Initial" = 1
    arity "Suffix" = 2

spec :: Spec
spec = do
  describe "runInterpretation" $ do
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "abc" `shouldBe` "xaabcbbccc"
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "ab" `shouldBe` "xaabbb"
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "c" `shouldBe` "xcc"
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "x" `shouldBe` "xxx"
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "q" `shouldBe` "xqq"
    it "should return the correct output" $ do
      runInterpretation squareInterpretation "" `shouldBe` "x"

