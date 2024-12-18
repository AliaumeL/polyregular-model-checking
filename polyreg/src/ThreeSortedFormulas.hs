{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ThreeSortedFormulas where

import QuantifierFree

import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

-- This module contains a (First-order) logic with three sorts:
-- a sort     (Pos) of positions, 
-- a sort     (Boolean) of booleans (True, False)
-- and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag | Boolean
  deriving (Show, Eq)

data Quant = Exists | Forall 
  deriving (Show, Eq)

data Var   = In    String 
           | Out   String 
           | Local Int String 
    deriving (Show, Eq)


data Formula tag alphabet = 
    -- Constants
      FConst Bool
    -- Boolean variables
    | FVar Var
    -- Binary operations
    | FBin BinOp (Formula tag alphabet) (Formula tag alphabet)
    -- Unary negation
    | FNot (Formula tag alphabet)
    -- Q x : T. φ. /!\ the "string" is only for debug purposes /!\
    | FQuant Quant String Sort (Formula tag alphabet)
    -- l(x)  (tag Variable x equals tag l)
    | FTag Var tag
    -- a(x)  (position Variable x has letter a)
    | FLetter Var alphabet
    -- Position tests (equality, <=, <, >, >=)
    | FTestPos TestOp Var Var
  deriving (Show, Eq)

andList :: [Formula tag alphabet] -> Formula tag alphabet
andList [] = FConst True
andList [x] = x
andList (x:xs) = FBin Conj x (andList xs)

orList :: [Formula tag alphabet] -> Formula tag alphabet
orList [] = FConst False
orList [x] = x
orList (x:xs) = FBin Disj x (orList xs)

quantifyList :: [(String, Sort, Quant)] -> Formula tag alphabet -> Formula tag alphabet
quantifyList [] f = f
quantifyList ((x, s, q):xs) f = FQuant q x s (quantifyList xs f)

-- | apply f to every Variable in the formula
-- f is given the current quantifier depth and the Variable name
mapVars :: (Int -> Var -> Var) -> Formula tag alphabet -> Formula tag alphabet
mapVars f = mapVars' f 0
    where
        mapVars' :: (Int -> Var -> Var) -> Int -> Formula tag alphabet -> Formula tag alphabet
        mapVars' f d (FConst b) = FConst b
        mapVars' f d (FVar x) = FVar $ f d x
        mapVars' f d (FBin op l r) = FBin op (mapVars' f d l) (mapVars' f d r)
        mapVars' f d (FNot l) = FNot (mapVars' f d l)
        mapVars' f d (FQuant q x s l) = FQuant q x s (mapVars' f (d+1) l)
        mapVars' f d (FTag x t) = FTag (f d x) t
        mapVars' f d (FLetter x l) = FLetter (f d x) l
        mapVars' f d (FTestPos t x y) = FTestPos t (f d x) (f d y)


-- | remap output Variables to either the identity or a "new" Variable
-- given by a string (for debugging purposes) and an integer (for de bruin indices)
quantOutVars :: (String -> Maybe (Int, String)) -> Formula tag alphabet -> Formula tag alphabet
quantOutVars f = mapVars g
    where
        g :: Int -> Var -> Var
        g d (Out x) = case f x of
                        Just (i, y) -> Local (i + d) y
                        Nothing     -> Out x
        g d x = x

quantInVars :: (String -> Maybe (Int, String)) -> Formula tag alphabet -> Formula tag alphabet
quantInVars f = mapVars g
    where
        g :: Int -> Var -> Var
        g d (In x) = case f x of
                        Just (i, y) -> Local (i + d) y
                        Nothing     -> In x
        g d x = x


-- | A formula seen as a morphism in the category of something
-- so that they can be composed.
data WrappedFormula tag alphabet = WrappedFormula {
    formula    :: Formula tag alphabet,
    types      :: Map String Sort,
    inputVars  :: Set String,
    outputVars :: Set String
} deriving (Show, Eq)

instance Semigroup (WrappedFormula tag alphabet) where
    (WrappedFormula φ iφ oφ mφ) <> (WrappedFormula ψ iψ oψ mψ) = 
        undefined

instance Monoid (WrappedFormula tag alphabet) where
    mempty = undefined 


prettyPrintQuant :: Quant -> String
prettyPrintQuant Exists = "∃"
prettyPrintQuant Forall = "∀"

