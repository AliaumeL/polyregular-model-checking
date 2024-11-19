module TwoSortedFormulas where


import QuantifierFree

-- This module contains a (First-order) logic with two sorts a sort (Pos) of
-- positions, and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag
  deriving (Show, Eq)


data Quant = Exists | Forall 
  deriving (Show, Eq)

data Formula tag alphabet = 
      FTrue
    | FFalse
    | FBin BinOp (Formula tag alphabet) (Formula tag alphabet)
    | FNot (Formula tag alphabet)
    -- Q x : T. φ
    | FQuant Quant String Sort (Formula tag alphabet)
    -- l(x)
    | FTag String tag
    -- a(x)
    | FLetter String alphabet
    -- Position tests (equality, <=, <, >, >=)
    | FTestPos  TestOp String String
  deriving (Show, Eq)

andList :: [Formula tag alphabet] -> Formula tag alphabet
andList [] = FTrue
andList [x] = x
andList (x:xs) = FBin Conj x (andList xs)

orList :: [Formula tag alphabet] -> Formula tag alphabet
orList [] = FFalse
orList [x] = x
orList (x:xs) = FBin Disj x (orList xs)

quantifyList :: [(String, Sort, Quant)] -> Formula tag alphabet -> Formula tag alphabet
quantifyList [] f = f
quantifyList ((x, s, q):xs) f = FQuant q x s (quantifyList xs f)
