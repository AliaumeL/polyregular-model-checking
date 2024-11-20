{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module TwoSortedFormulas where


import QuantifierFree

import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)
import Data.Map (Map)
import qualified Data.Map as Map

-- This module contains a (First-order) logic with two sorts a sort (Pos) of
-- positions, and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag
  deriving (Show, Eq)


data Quant = Exists | Forall 
  deriving (Show, Eq)

prettyPrintQuant :: Quant -> String
prettyPrintQuant Exists = "∃"
prettyPrintQuant Forall = "∀"

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

prettyPrint :: (Show tag, Show alphabet) => Formula tag alphabet -> String
prettyPrint FTrue = "⊤"
prettyPrint FFalse = "⊥"
prettyPrint (FBin op l r) = "(" ++ prettyPrint l ++ " " ++ prettyPrintBin op ++ " " ++ prettyPrint r ++ ")"
prettyPrint (FNot f) = "¬" ++ prettyPrint f
prettyPrint (FQuant q x s f) = prettyPrintQuant q ++ " " ++ x ++ " : " ++ show s ++ ". " ++ prettyPrint f
prettyPrint (FTag x t) = x ++ " ∈ " ++ show t
prettyPrint (FLetter x l) = x ++ " = " ++ show l
prettyPrint (FTestPos t x y) = x ++ " " ++ prettyPrintOp t ++ " " ++ y


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


type TagName = String

class (Monad m) => MonadTSF m where
    getPos    :: String -> m Int
    getCharAt :: String -> m Char
    getTag    :: String -> m TagName
    withQuant :: Quant -> String -> Sort -> m Bool -> m Bool


evalFormulaM :: (MonadTSF m) => Formula TagName Char -> m Bool
evalFormulaM FTrue = return True
evalFormulaM FFalse = return False
evalFormulaM (FBin op l r) = binOpSemantics op <$> evalFormulaM l <*> evalFormulaM r
evalFormulaM (FTestPos t x y) = testOpSemantics t <$> getPos x <*> getPos y
evalFormulaM (FNot l) = not <$> evalFormulaM l
evalFormulaM (FTag x t) = (== t) <$> getTag x
evalFormulaM (FLetter x l) = (== l) <$> getCharAt x
evalFormulaM (FQuant q x s f) = withQuant q x s (evalFormulaM f)

evalFormula :: String -> [TagName] -> Formula TagName Char -> Bool
evalFormula word tags f = runReader (evalFormulaM f) state
    where
        state = FormulaState word Map.empty Map.empty tags


data FormulaState tag = FormulaState {
    word     :: String,
    pos      :: Map String Int,
    tags     :: Map String tag,
    allTags  :: [tag]
} deriving (Eq,Show)

type FormulaReader = Reader (FormulaState TagName)

instance MonadTSF FormulaReader where
    getPos x = do 
        pos <- asks pos
        case Map.lookup x pos of
            Just i -> return i
            Nothing -> error $ "Variable " ++ x ++ " not found"
    getCharAt x = do 
        pos <- getPos x
        w   <- asks word
        return $ w !! pos
    getTag x = do 
        ts <- asks tags
        case Map.lookup x ts of
            Just i -> return i
            Nothing -> error $ "Variable " ++ x ++ " not found"
        
    withQuant quant x s m = case (s,quant) of 
                                (Tag,Exists) -> valuesTag >>= anyM (\v -> localLetTag x v m)
                                (Pos,Exists) -> valuesPos >>= anyM (\v -> localLetPos x v m) 
                                (Tag,Forall) -> valuesTag >>= allM (\v -> localLetTag x v m)
                                (Pos,Forall) -> valuesPos >>= allM (\v -> localLetPos x v m)
        where
            localLetTag x v m = do 
                ts <- asks tags
                local (\s -> s { tags = Map.insert x v ts }) m 

            localLetPos x v m = do
                ps <- asks pos
                local (\s -> s { pos = Map.insert x v ps }) m

            valuesTag = asks allTags
            valuesPos = do
                w <- asks word
                return $ [0..length w - 1]
