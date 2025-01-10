{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Formulas (Sort(..), Quant(..), Var(..), Formula(..), Value(..),
andList, orList, quantifyList, mapInVars, mapOutVars, mapVars,
substituteBooleanVar, freeVars, prettyPrintFormula, 
quantOutVars, quantInVars, injectTags, evalFormula, evalFormulaWithFreeVars)
where

import QuantifierFree

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)

import qualified SimpleForPrograms as SFP

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

-- This module contains a (First-order) logic with three sorts:
-- a sort     (Pos) of positions, 
-- a sort     (Boolean) of booleans (True, False)
-- and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag | Boolean
  deriving (Show, Eq, Ord)

data Quant = Exists | Forall 
  deriving (Show, Eq, Ord)

data Var   = In    String 
           | Out   String 
           | Local Int String 
    deriving (Show, Eq, Ord) 


data Formula tag  = 
    -- Constants
      FConst Bool
    -- Boolean variables
    | FVar Var
    -- Binary operations
    | FBin BinOp (Formula tag) (Formula tag)
    -- Unary negation
    | FNot (Formula tag)
    -- Q x : T. φ. /!\ the "string" is only for debug purposes /!\
    | FQuant Quant String Sort (Formula tag )
    -- l(x)  (tag Variable x equals tag l)
    | FTag Var tag
    -- a(x)  (position Variable x has letter a)
    | FLetter Var Char
    -- Position tests (equality, <=, <, >, >=)
    | FTestPos TestOp Var Var
    -- We have to be able to test if a position is "real"
    -- This is needed for the later "pullBack" construction
    -- where we will quantify over "real+imaginary" positions
    | FRealPos Var 
    -- It will also be super useful to have a "predecessor"
    -- relation for positions: this can be efficiently
    -- converted in MONA using (p - 1) = q
    -- and also in most SMT solvers
    | FPredPos Var Var
  deriving (Show, Eq, Ord)

injectTags :: Formula () -> Formula t
injectTags (FConst b) = FConst b
injectTags (FVar x) = FVar x
injectTags (FBin op l r) = FBin op (injectTags l) (injectTags r)
injectTags (FNot l) = FNot (injectTags l)
injectTags (FQuant q x s l) = FQuant q x s (injectTags l)
injectTags (FTag _ _) = FConst False
injectTags (FLetter x l) = FLetter x l
injectTags (FTestPos t x y) = FTestPos t x y
injectTags (FRealPos x) = FRealPos x
injectTags (FPredPos x y) = FPredPos x y



andList :: [Formula tag ] -> Formula tag 
andList [] = FConst True
andList [x] = x
andList (x:xs) = FBin Conj x (andList xs)

orList :: [Formula tag ] -> Formula tag 
orList [] = FConst False
orList [x] = x
orList (x:xs) = FBin Disj x (orList xs)

quantifyList :: [(String, Sort, Quant)] -> Formula tag  -> Formula tag 
quantifyList [] f = f
quantifyList ((x, s, q):xs) f = FQuant q x s (quantifyList xs f)



substituteBooleanVar :: (Var -> Formula tag ) -> Formula tag  -> Formula tag 
substituteBooleanVar f (FConst x) = FConst x
substituteBooleanVar f (FVar x) = f x
substituteBooleanVar f (FBin op l r) = FBin op (substituteBooleanVar f l) (substituteBooleanVar f r)
substituteBooleanVar f (FNot l) = FNot (substituteBooleanVar f l)
substituteBooleanVar f (FQuant q x s l) = FQuant q x s (substituteBooleanVar f l)
substituteBooleanVar f (FTag x t) = FTag x t
substituteBooleanVar f (FLetter x l) = FLetter x l
substituteBooleanVar f (FTestPos t x y) = FTestPos t x y




-- | apply f to every Variable in the formula
-- f is given the current quantifier depth and the Variable name
mapVars :: (Int -> Var -> Var) -> Formula tag  -> Formula tag 
mapVars f = mapVars' f 0
    where
        mapVars' :: (Int -> Var -> Var) -> Int -> Formula tag  -> Formula tag 
        mapVars' f d (FConst b) = FConst b
        mapVars' f d (FVar x) = FVar $ f d x
        mapVars' f d (FBin op l r) = FBin op (mapVars' f d l) (mapVars' f d r)
        mapVars' f d (FNot l) = FNot (mapVars' f d l)
        mapVars' f d (FQuant q x s l) = FQuant q x s (mapVars' f (d+1) l)
        mapVars' f d (FTag x t) = FTag (f d x) t
        mapVars' f d (FLetter x l) = FLetter (f d x) l
        mapVars' f d (FTestPos t x y) = FTestPos t (f d x) (f d y)

mapOutVars :: (Int -> String -> Var) -> Formula tag  -> Formula tag
mapOutVars f = mapVars g
    where
        g :: Int -> Var -> Var
        g d (Out x) = f d x
        g d x = x

mapInVars :: (Int -> String -> Var) -> Formula tag  -> Formula tag
mapInVars f = mapVars g
    where
        g :: Int -> Var -> Var
        g d (In x) = f d x
        g d x = x

-- | remap output Variables to either the identity or a "new" Variable
-- given by a string (for debugging purposes) and an integer (for de bruin indices)
quantOutVars :: (String -> Maybe (Int, String)) -> Formula tag  -> Formula tag 
quantOutVars f = mapOutVars g
    where
        g :: Int -> String -> Var
        g d x = case f x of
                    Just (i, y) -> Local (i + d) y
                    Nothing     -> Out x

quantInVars :: (String -> Maybe (Int, String)) -> Formula tag  -> Formula tag 
quantInVars f = mapInVars g
    where
        g :: Int -> String -> Var
        g d x = case f x of
                    Just (i, y) -> Local (i + d) y
                    Nothing     -> In x


freeVars :: Formula tag  -> (Map String Sort, Map String Sort)
freeVars (FVar (In x))  = (M.singleton x Boolean, M.empty)
freeVars (FVar (Out x)) = (M.empty, M.singleton x Boolean)
freeVars (FBin _ l r) = (sIn, sOut)
    where
        (sInL, sOutL) = freeVars l
        (sInR, sOutR) = freeVars r
        sIn = sInL `M.union` sInR
        sOut = sOutL `M.union` sOutR
freeVars (FNot l) = freeVars l
freeVars (FQuant _ _ _ l) = freeVars l
freeVars (FTag (In x) _) = (M.singleton x Tag, M.empty)
freeVars (FTag (Out x) _) = (M.empty, M.singleton x Tag)
freeVars (FLetter (In x) _) = (M.singleton x Pos, M.empty)
freeVars (FLetter (Out x) _) = (M.empty, M.singleton x Pos)
freeVars (FTestPos _ (In x) (In y)) =  (M.singleton x Pos `M.union` M.singleton y Pos, M.empty)
freeVars (FTestPos _ (Out x) (In y)) =  (M.singleton y Pos, M.singleton x Pos)
freeVars (FTestPos _ (In x) (Out y)) = (M.singleton x Pos, M.singleton y Pos)
freeVars (FTestPos _ (Out x) (Out y)) =  (M.empty, M.singleton x Pos `M.union` M.singleton y Pos)
freeVars _ = (M.empty, M.empty)

prettyPrintQuant :: Quant -> String
prettyPrintQuant Exists = "∃"
prettyPrintQuant Forall = "∀"

prettyPrintSort :: Sort -> String
prettyPrintSort Pos = "P"
prettyPrintSort Tag = "T"
prettyPrintSort Boolean = "B"

prettyPrintVar :: Var -> String
prettyPrintVar (In x) = x ++ show "[in]"
prettyPrintVar (Out x) = x  ++ show "[out]"
prettyPrintVar (Local i x) = show i ++ "(" ++ x ++ ")"

prettyPrintFormula :: Show tag => Formula tag  -> String
prettyPrintFormula (FConst b) = if b then "⊤" else "⊥"
prettyPrintFormula (FVar x) = prettyPrintVar x
prettyPrintFormula (FBin op l r) = "(" ++ prettyPrintFormula l ++ prettyPrintBin op ++ prettyPrintFormula r ++ ")"
prettyPrintFormula (FNot l) = "¬" ++ prettyPrintFormula l
prettyPrintFormula (FQuant q x s l) = prettyPrintQuant q ++ " " ++ x ++ " : " ++ prettyPrintSort s ++ ". " ++ prettyPrintFormula l
prettyPrintFormula (FTag x t) = prettyPrintVar x ++ " ∈ " ++ show t
prettyPrintFormula (FLetter x l) = [l] ++ "(" ++ prettyPrintVar x ++ ")"
prettyPrintFormula (FTestPos t x y) = prettyPrintVar x ++ " " ++ prettyPrintOp t ++ " " ++ prettyPrintVar y
prettyPrintFormula (FRealPos x) = "real(" ++ prettyPrintVar x ++ ")"
prettyPrintFormula (FPredPos x y) = prettyPrintVar x ++ " = " ++ prettyPrintVar y ++ " - 1"


-- formula evaluation

data Value = PosVal Int | BoolVal Bool | TagVal String deriving(Eq,Show)
newtype DBIndex = DBIndex Int deriving(Eq,Show,Num)

class (Monad m) => MonadEval m where
    getFreeVar    :: String -> m Value
    withVariable  :: Value -> m a -> m a
    quantify      :: Quant -> Sort -> m Bool -> m Bool
    getBoundVar   :: DBIndex -> m Value
    getCharAt     :: DBIndex -> m Char

data EvalState = EvalState {
    freeVarsDict :: Map String Value,
    word :: String,
    vars :: [Value],
    tags :: [String]
} deriving(Eq,Show)

newtype EvalM a = EvalM (State EvalState a) 
    deriving(Functor, Applicative, Monad, MonadState EvalState)


runEvalM :: EvalM a -> EvalState -> a
runEvalM (EvalM m) s = evalState m s

quantToAgg :: Quant -> [Bool] -> Bool
quantToAgg Exists = any id
quantToAgg Forall = all id

instance MonadEval EvalM where
    withVariable v m = do 
        vars <- gets vars
        modify (\s -> s { vars = v : vars })
        v <- m 
        modify (\s -> s { vars = vars })
        return v

    getCharAt (DBIndex i) = do
        w <- gets word
        return (w !! i)

    getBoundVar (DBIndex i) = do
        vars <- gets vars
        return (vars !! i)

    getFreeVar x = do
        dict <- gets freeVarsDict
        case M.lookup x dict of
            Just v -> return v
            Nothing -> error $ "Free variable " ++ x ++ " not found"

    quantify quant Pos m = do
        w <- gets word 
        let pos = map PosVal [0.. (length w - 1)]
        bs <- mapM (\p -> withVariable p m) pos
        return . quantToAgg quant $ bs

    quantify quant Boolean m = do
        bs <- mapM (\p -> withVariable p m) [BoolVal True, BoolVal False]
        return . quantToAgg quant $ bs

    quantify quant Tag m = do
        tgs <- gets tags
        bs  <- mapM (\t -> withVariable (TagVal t) m) tgs
        return . quantToAgg quant $ bs

getVar :: (MonadEval m) => Var -> m Value
getVar (In x) = getFreeVar x
getVar (Out x) = error "Free output variable"
getVar (Local i _) = getBoundVar (DBIndex i)


evalFormulaM :: (MonadEval m) => Formula String -> m Bool
evalFormulaM (FConst b) = return b
evalFormulaM (FVar v) = do
    v <- getVar v
    case v of
        BoolVal b -> return b
        _ -> error "Type error"
evalFormulaM (FVar (In _))  = error "Free input variable"
evalFormulaM (FVar (Out _)) = error "Free output variable"
evalFormulaM (FBin Conj l r) = do
    l' <- evalFormulaM l
    r' <- evalFormulaM r
    return $ l' && r'
evalFormulaM (FBin Disj l r) = do
    l' <- evalFormulaM l
    r' <- evalFormulaM r
    return $ l' || r'
evalFormulaM (FNot l) = do
    l' <- evalFormulaM l
    return $ not l'
evalFormulaM (FQuant q _ s l) = quantify q s (evalFormulaM l)
evalFormulaM (FTag v t) = do
    v <- getVar v
    case v of
        TagVal t' -> return $ t == t'
        _ -> error "Type error"
evalFormulaM (FLetter v l) = do
    v <- getVar v
    case v of 
        PosVal x -> do
            c <- getCharAt (DBIndex x)
            return $ c == l
        _ -> error "Type error"
    
evalFormulaM (FTestPos op v1 v2) = do
    x' <- getVar v1
    y' <- getVar v2
    case (x', y') of
        (PosVal x'', PosVal y'') -> return $ testOpSemantics op x'' y''
        _ -> error "Type error"
evalFormulaM (FRealPos v) = do
    x' <- getVar v
    case x' of
        PosVal x'' -> return $ x'' >= 0
        _ -> error "Type error"
evalFormulaM (FPredPos v1 v2) = do
    x' <- getVar v1
    y' <- getVar v2
    case (x', y') of
        (PosVal x'', PosVal y'') -> return $ x'' == y'' + 1
        _ -> error "Type error"
evalFormulaM f = error $ "Not implemented: " ++ show f


evalFormula :: Formula String -> [String] ->  String -> Bool
evalFormula f tags w = runEvalM (evalFormulaM f) (EvalState M.empty w [] tags)

evalFormulaWithFreeVars :: Formula String -> [(String, Value)] -> [String] -> String -> Bool
evalFormulaWithFreeVars f freeVars tags w = runEvalM (evalFormulaM f) (EvalState (M.fromList freeVars) w [] tags)


-- TODO: Extract the values of free variables