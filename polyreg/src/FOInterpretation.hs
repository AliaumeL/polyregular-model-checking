{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module FOInterpretation where

import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)
import Data.Map (Map)
import Data.List (sortBy)
import qualified Data.Map as Map

import QuantifierFree

type VarName = String
type TagName = String


data Quant  = Exists | Forall deriving (Show, Eq)

data Formula var alphabet = 
               FOTrue
             | FOFalse
             | FOTestPos TestOp var var
             | FOCharAt var alphabet
             | FONot (Formula var alphabet)
             | FOBin BinOp (Formula var alphabet) (Formula var alphabet)
             | FOQuant Quant var (Formula var alphabet)
             deriving (Eq,Show)

data FOInterpretation var alphabet tag = Interpretation {
    tags           :: [tag],
    outputLetters  :: [alphabet],
    domainFormula  :: tag -> [var] -> Formula var alphabet,
    orderFormula   :: tag -> tag -> [var] -> [var] -> Formula var alphabet,
    labelFormula   :: tag -> alphabet -> [var] -> Formula var alphabet,
    copyFormula    :: tag -> Int -> [var] -> Formula var alphabet,
    arity          :: tag -> Int,
    maxArity       :: Int
}


-- Now, we directly evaluate FO Interpretations using the naïve semantics
-- so that we can check our transformations.

data FormulaState = FormulaState {
    vars :: Map VarName Int,
    word :: [Char]
}

class Monad m => MonadFO m where
    foGetPos  :: VarName -> m Int
    foGetChar :: VarName -> m Char
    foLetName :: VarName -> Int -> m a -> m a
    foAny     :: VarName -> m Bool -> m Bool
    foAll     :: VarName -> m Bool -> m Bool

instance MonadFO (Reader FormulaState) where
    foGetPos x = do
        vars <- asks vars
        case Map.lookup x vars of
            Just i -> return i
            Nothing -> error $ "Variable " ++ x ++ " not found"
    foGetChar x = do
        i <- foGetPos x
        word <- asks word
        return $ word !! i
    foLetName x i m = do
        vars <- asks vars
        local (\s -> s { vars = Map.insert x i vars }) m
    foAny x m = do
        i <- foGetPos x
        word <- asks word
        anyM (\j -> foLetName x j m) [0..length word - 1]
    foAll x m = do
        i <- foGetPos x
        word <- asks word
        allM (\j -> foLetName x j m) [0..length word - 1]

evalFormulaM :: (MonadFO m) => Formula VarName Char -> m Bool
evalFormulaM FOTrue = return True
evalFormulaM FOFalse = return False
evalFormulaM (FOTestPos t  x y) = do
    posx <- foGetPos x
    posy <- foGetPos y
    return . testOpSemantics t posx $ posy
evalFormulaM (FOCharAt x c) = do
    charx <- foGetChar x
    return $ charx == c
evalFormulaM (FONot f) = do
    b <- evalFormulaM f
    return $ not b
evalFormulaM (FOBin op f1 f2) = do
    b1 <- evalFormulaM f1
    b2 <- evalFormulaM f2
    return $ binOpSemantics op b1 b2
evalFormulaM (FOQuant Exists name f) = foAny name $ evalFormulaM f
evalFormulaM (FOQuant Forall name f) = foAll name $ evalFormulaM f

evalFormulaInContext :: FormulaState -> Formula VarName Char -> Bool
evalFormulaInContext s f = runReader (evalFormulaM f) s

evalFormula :: Formula VarName Char -> Bool
evalFormula f = evalFormulaInContext (FormulaState Map.empty []) f



evalInterpretation :: FOInterpretation VarName Char TagName -> String -> String
evalInterpretation interp word = map (\(_,_,c) -> c) $ positionsFilteredSortedWithChars
    where
        comparePositions :: (TagName, [Int]) -> (TagName, [Int]) -> Ordering
        comparePositions (t1,p1) (t2,p2) = if t1 == t2 && p1 == p2 then 
                                            EQ
                                           else case cmp of 
                                            True -> LT
                                            False -> GT
            where
                vars1 = map (\i -> "x" ++ show i) [1..length p1]
                vars2 = map (\i -> "y" ++ show i) [1..length p2]
                vars  = vars1 ++ vars2
                state = FormulaState (Map.fromList $ zip vars (p1 ++ p2)) word
                cmp = evalFormulaInContext state $ orderFormula interp t1 t2 vars1 vars2

        computePresence :: (TagName, [Int]) -> Bool
        computePresence (tag, pos) = evalFormulaInContext state $ domainFormula interp tag vars
            where
                vars = map (\i -> "x" ++ show i) [1..length pos]
                state = FormulaState (Map.fromList $ zip vars pos) word

        computeChar :: (TagName, [Int]) -> Char
        computeChar (tag, pos) = fst . head . filter snd $ shouldCopy ++ letters
            where
                vars = map (\i -> "x" ++ show i) [1..length pos]
                state = FormulaState (Map.fromList $ zip vars pos) word

                shouldCopy :: [(Char, Bool)]
                shouldCopy = do 
                    i <- [0..length pos - 1]
                    return $ (word !! i, evalFormulaInContext state $ copyFormula interp tag i vars)

                letters :: [(Char, Bool)]
                letters    = do 
                    c <- outputLetters interp
                    return $ (c, evalFormulaInContext state $ labelFormula interp tag c vars)
                    

        positionsTag :: TagName -> [[Int]]
        positionsTag tag = 
            let n = arity interp tag
            in  sequence $ replicate n [0..length word - 1]

        positions :: [(TagName, [Int])]
        positions = concatMap (\tag -> map (\pos -> (tag, pos)) $ positionsTag tag) $ tags interp

        positionsFiltered :: [(TagName, [Int])]
        positionsFiltered = filter computePresence positions

        
        positionsFilteredSorted :: [(TagName, [Int])]
        positionsFilteredSorted = sortBy comparePositions positionsFiltered


        positionsFilteredSortedWithChars :: [(TagName, [Int], Char)]
        positionsFilteredSortedWithChars = do
            (tag, pos) <- positionsFilteredSorted
            return (tag, pos, computeChar (tag, pos))
