module TwoSortedFormulas where

-- This module contains a (First-order) logic with two sorts a sort (Pos) of
-- positions, and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag
  deriving (Show, Eq)

data BinOp = And | Or | Not | Implies
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
    -- Position equality (x = y)
    | FEqual String String
    -- Position inequality (x <= y)
    | FLeq String String
  deriving (Show, Eq)
