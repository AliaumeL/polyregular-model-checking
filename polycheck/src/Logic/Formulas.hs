{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Formulas (Sort(..), Quant(..), Var(..), Formula(..), Value(..),
    extractLetters,
    shiftVar,
    quantifierDepth,
    formulaSize,
    simplifyFormula,
    addRealPositions,
    andList, orList, quantifyList, mapInVars, mapOutVars, mapVars,
    nestQuantVars, nestQuantVar, mapTags,
    substituteBooleanVar, freeVars, prettyPrintFormula, 
    quantInOutVarsGeneric,
    quantOutVars, quantInVars, injectTags, ignoreTags, removeTags, evalFormula, evalFormulaWithFreeVars, 
    showFormulaGeneric
)
where

import Logic.QuantifierFree

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)

import qualified ForPrograms.Simple as SFP

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as S

-- This module contains a (First-order) logic with three sorts:
-- a sort     (Pos) of positions, 
-- a sort     (Boolean) of booleans (True, False)
-- and a sort (Tag) of finitely many tags.

data Sort = Pos | Tag | Boolean
  deriving (Show, Eq, Ord, Read)

data Quant = Exists | Forall 
  deriving (Show, Eq, Ord, Read)

data Var   = In    String 
           | Out   String 
           | Local Int String 
    deriving (Show, Eq, Ord, Read) 


shiftVar :: Int -> Var -> Var
shiftVar _ (In x) = In x
shiftVar _ (Out x) = Out x
shiftVar i (Local j x) = Local (j + i) x

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
  deriving (Show, Eq, Ord, Read)


varEquality :: Var -> Var -> Bool
varEquality (Local i _) (Local j _) = i == j
varEquality (In x) (In y) = x == y
varEquality (Out x) (Out y) = x == y
varEquality _ _ = False


simplifyFormula :: (Eq tag) => Formula tag -> Formula tag
simplifyFormula = fixpoint simplifyOnce
    where
        fixpoint :: Eq a => (a -> a) -> a -> a
        fixpoint f x = let x' = f x in if x == x' then x else fixpoint f x'
        
        simplifyOnce  (FBin Disj (FTestPos Eq x y) (FTestPos Lt x' y')) | x == x' && y == y' = FTestPos Le x y
        simplifyOnce  (FBin Disj (FTestPos Eq x y) (FTestPos Gt x' y')) | x == x' && y == y' = FTestPos Ge x y
        simplifyOnce  (FBin Conj (FConst True) x)   = simplifyOnce x
        simplifyOnce  (FBin Conj x (FConst True))   = simplifyOnce x
        simplifyOnce  (FBin Conj (FConst False) x)  = FConst False
        simplifyOnce  (FBin Conj x (FConst False))  = FConst False
        simplifyOnce  (FBin Disj (FConst False) x)  = simplifyOnce x
        simplifyOnce  (FBin Disj x (FConst False))  = simplifyOnce x
        simplifyOnce  (FBin Disj (FConst True) x)   = FConst True
        simplifyOnce  (FBin Impl (FConst True) x)   = simplifyOnce x
        simplifyOnce  (FBin Impl x (FConst False))  = simplifyOnce (FNot x)
        simplifyOnce  (FBin Impl (FConst False) x)  = FConst True
        simplifyOnce  (FBin Impl x (FConst True))   = FConst True
        simplifyOnce  (FBin Disj x (FConst True))   = FConst True
        simplifyOnce  (FBin Equiv (FConst True) x)  = simplifyOnce x
        simplifyOnce  (FBin Equiv (FConst False) x) = simplifyOnce (FNot x)
        simplifyOnce  (FBin Equiv x (FConst True))  = simplifyOnce x
        simplifyOnce  (FBin Equiv x (FConst False)) = simplifyOnce (FNot x)
        simplifyOnce  (FTestPos Eq  x y) | x == y = FConst True
        simplifyOnce  (FTestPos Le  x y) | x == y = FConst True
        simplifyOnce  (FTestPos Ge  x y) | x == y = FConst True
        simplifyOnce  (FTestPos Neq x y) | x == y = FConst False
        simplifyOnce  (FTestPos Lt  x y) | x == y = FConst False
        simplifyOnce  (FTestPos Gt  x y) | x == y = FConst False
        simplifyOnce  (FNot (FConst a))            = FConst (not a)
        simplifyOnce  (FBin o a b) = FBin o (simplifyOnce a) (simplifyOnce b)
        simplifyOnce  (FNot a) = FNot (simplifyOnce a)
        simplifyOnce  (FQuant q x s a) = FQuant q x s (simplifyOnce a)
        simplifyOnce  x = x



quantifierDepth :: Formula tag -> Int
quantifierDepth (FConst _) = 0
quantifierDepth (FVar _) = 0
quantifierDepth (FBin _ l r) = max (quantifierDepth l) (quantifierDepth r)
quantifierDepth (FNot l) = quantifierDepth l
quantifierDepth (FQuant _ _ _ l) = 1 + quantifierDepth l    
quantifierDepth (FTag _ _) = 0
quantifierDepth (FLetter _ _) = 0
quantifierDepth (FTestPos _ _ _) = 0
quantifierDepth (FRealPos _) = 0

formulaSize :: Formula tag -> Int
formulaSize (FConst _) = 1
formulaSize (FVar _) = 1
formulaSize (FBin _ l r) = 1 + formulaSize l + formulaSize r
formulaSize (FNot l) = 1 + formulaSize l
formulaSize (FQuant _ _ _ l) = 1 + formulaSize l
formulaSize (FTag _ _) = 1
formulaSize (FLetter _ _) = 1
formulaSize (FTestPos _ _ _) = 1
formulaSize (FRealPos _) = 1



showFormulaGeneric :: Formula tag -> String 
showFormulaGeneric (FConst b) = if b then "⊤" else "⊥"
showFormulaGeneric (FVar x) = show x
showFormulaGeneric (FBin op l r) = "(" ++ showFormulaGeneric l ++ show op ++ showFormulaGeneric r ++ ")"
showFormulaGeneric (FNot l) = "¬" ++ showFormulaGeneric l
showFormulaGeneric (FQuant q x s l) = show q ++ " " ++ x ++ " : " ++ show s ++ ". " ++ showFormulaGeneric l
showFormulaGeneric (FTag x t) = show x ++ " ∈ " ++ " SomeTag"
showFormulaGeneric (FLetter x l) = show x ++ " = " ++ show l
showFormulaGeneric (FTestPos t x y) = show x ++ " " ++ show t ++ " " ++ show y
showFormulaGeneric (FRealPos x) = "real(" ++ show x ++ ")"


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

ignoreTags :: Formula t -> Formula ()
ignoreTags (FConst b) = FConst b
ignoreTags (FVar x) = FVar x
ignoreTags (FBin op l r) = FBin op (ignoreTags l) (ignoreTags r)
ignoreTags (FNot l) = FNot (ignoreTags l)
ignoreTags (FQuant q x s l) = FQuant q x s (ignoreTags l)
ignoreTags (FTag x _) = FTag x ()
ignoreTags (FLetter x l) = FLetter x l
ignoreTags (FTestPos t x y) = FTestPos t x y
ignoreTags (FRealPos x) = FRealPos x

removeTags :: Formula t -> Either String (Formula ())
removeTags (FConst b) = Right $ FConst b
removeTags (FVar x) = Right $ FVar x
removeTags (FBin op l r) = do
    l' <- removeTags l
    r' <- removeTags r
    return $ FBin op l' r'
removeTags (FNot l) = do
    l' <- removeTags l
    return $ FNot l'
removeTags (FQuant q x Tag l) = Left "Cannot remove tags from quantified variables"
removeTags (FQuant q x s l) = do
    l' <- removeTags l
    return $ FQuant q x s l'
removeTags (FTag _ _) = Left "Cannot remove tags"
removeTags (FLetter x l) = Right $ FLetter x l
removeTags (FTestPos t x y) = Right $ FTestPos t x y
removeTags (FRealPos x) = Right $ FRealPos x


    


addRealPositions :: Formula tag -> Formula tag
addRealPositions (FConst b) = FConst b
addRealPositions (FVar x) = FVar x
addRealPositions (FBin op l r) = FBin op (addRealPositions l) (addRealPositions r)
addRealPositions (FNot l) = FNot (addRealPositions l)
addRealPositions (FQuant Exists x Pos l) = FQuant Exists x Pos (FBin Conj (FRealPos (Local 0 x)) (addRealPositions l))
addRealPositions (FQuant Forall x Pos l) = FQuant Forall x Pos (FBin Impl (FRealPos (Local 0 x)) (addRealPositions l))
addRealPositions (FQuant q x s l) = FQuant q x s (addRealPositions l)
addRealPositions (FTag x t) = FTag x t
addRealPositions (FLetter x l) = FLetter x l
addRealPositions (FTestPos t x y) = FTestPos t x y
addRealPositions (FRealPos x) = FRealPos x



mapTags :: (t -> s) -> Formula t -> Formula s
mapTags _ (FConst b) = FConst b
mapTags _ (FVar x) = FVar x
mapTags f (FBin op l r) = FBin op (mapTags f l) (mapTags f r)
mapTags f (FNot l) = FNot (mapTags f l)
mapTags f (FQuant q x s l) = FQuant q x s (mapTags f l)
mapTags f (FTag v t) = FTag v (f t)
mapTags _ (FLetter x l) = FLetter x l
mapTags _ (FTestPos t x y) = FTestPos t x y
mapTags _ (FRealPos x) = FRealPos x



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
mapVars :: (Int -> Sort -> Var -> Var) -> Formula tag  -> Formula tag 
mapVars f = mapVars' f 0
    where
        mapVars' :: (Int -> Sort -> Var -> Var) -> Int -> Formula tag  -> Formula tag 
        mapVars' f d (FConst b) = FConst b
        mapVars' f d (FVar x) = FVar $ f d Boolean x
        mapVars' f d (FBin op l r) = FBin op (mapVars' f d l) (mapVars' f d r)
        mapVars' f d (FNot l) = FNot (mapVars' f d l)
        mapVars' f d (FQuant q x s l) = FQuant q x s (mapVars' f (d+1) l)
        mapVars' f d (FTag x t) = FTag (f d Tag x) t
        mapVars' f d (FLetter x l) = FLetter (f d Pos x) l
        mapVars' f d (FTestPos t x y) = FTestPos t (f d Pos x) (f d Pos y)

mapOutVars :: (Int -> Sort -> String -> Var) -> Formula tag  -> Formula tag
mapOutVars f = mapVars g
    where
        g :: Int -> Sort -> Var -> Var
        g d s (Out x) = f d s x
        g d s x = x

mapInVars :: (Int -> Sort -> String -> Var) -> Formula tag  -> Formula tag
mapInVars f = mapVars g
    where
        g :: Int -> Sort -> Var -> Var
        g d s (In x) = f d s x
        g d s x = x


quantInOutVarsGeneric :: (Sort -> String -> Maybe Var) ->
                         (Sort -> String -> Maybe Var) -> 
                         Formula tag  -> Formula tag
quantInOutVarsGeneric f g  = mapVars h
    where
        h :: Int -> Sort -> Var -> Var
        h d s (In x) = case f s x of
                        Just (Local i n) -> Local (i + d) n
                        Just x -> x
                        Nothing -> In x
        h d s (Out x) = case g s x of
                        Just (Local i n) -> Local (i + d) n
                        Just x -> x
                        Nothing -> Out x
        h _ _ x = x


-- | remap output Variables to either the identity or a "new" Variable
-- given by a string (for debugging purposes) and an integer (for de bruin indices)
quantOutVars :: (Sort -> String -> Maybe Var) -> Formula tag  -> Formula tag 
quantOutVars f = quantInOutVarsGeneric (\_ _ -> Nothing) f

quantInVars :: (Sort -> String -> Maybe Var) -> Formula tag  -> Formula tag 
quantInVars f = quantInOutVarsGeneric f (\_ _ -> Nothing)


varToFreeVars :: Var -> Sort -> (Map String Sort, Map String Sort)
varToFreeVars (In x) s = (M.singleton x s, M.empty)
varToFreeVars (Out x) s = (M.empty, M.singleton x s)
varToFreeVars (Local _ _) _ = (M.empty, M.empty)

freeVars :: Formula tag  -> (Map String Sort, Map String Sort)
freeVars (FVar v)  = varToFreeVars v Boolean
freeVars (FBin _ l r) = (sIn, sOut)
    where
        (sInL, sOutL) = freeVars l
        (sInR, sOutR) = freeVars r
        sIn = sInL `M.union` sInR
        sOut = sOutL `M.union` sOutR
freeVars (FNot l) = freeVars l
freeVars (FQuant _ _ _ l) = freeVars l
freeVars (FTag v _) = varToFreeVars v Tag
freeVars (FLetter v _) = varToFreeVars v Pos
freeVars (FTestPos _ v1 v2) = varToFreeVars v1 Pos <> varToFreeVars v2 Pos
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

nestQuantVar :: Int -> Var -> Var
nestQuantVar _ (In x) = In x
nestQuantVar _ (Out x) = Out x
nestQuantVar i (Local x s) = Local (x+i) s

nestQuantVars :: Int -> [Var] -> [Var]
nestQuantVars i = map (nestQuantVar i)

evalFormulaM :: (MonadEval m) => Formula String -> m Bool
evalFormulaM (FConst b) = return b
evalFormulaM (FVar v) = do
    v <- getVar v
    case v of
        BoolVal b -> return b
        _ -> error "Type error"
evalFormulaM (FVar (In _))  = error "Free input variable"
evalFormulaM (FVar (Out _)) = error "Free output variable"
evalFormulaM (FBin op l r) = do
    l' <- evalFormulaM l
    r' <- evalFormulaM r
    return $ binOpSemantics op l' r'
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
evalFormulaM f = error $ "Not implemented: " ++ show f


evalFormula :: Formula String -> [String] ->  String -> Bool
evalFormula f tags w = runEvalM (evalFormulaM f) (EvalState M.empty w [] tags)

evalFormulaWithFreeVars :: Formula String -> [(String, Value)] -> [String] -> String -> Bool
evalFormulaWithFreeVars f freeVars tags w = runEvalM (evalFormulaM f) (EvalState (M.fromList freeVars) w [] tags)


-- | Extract all the letter constants used in the formula
extractLetters :: Formula tag -> Set Char
extractLetters (FConst _) = S.empty
extractLetters (FVar _) = S.empty
extractLetters (FBin _ l r) = extractLetters l `S.union` extractLetters r
extractLetters (FNot l) = extractLetters l
extractLetters (FQuant _ _ _ l) = extractLetters l
extractLetters (FTag _ _) = S.empty
extractLetters (FLetter _ l) = S.singleton l
extractLetters (FTestPos _ _ _) = S.empty
extractLetters (FRealPos _) = S.empty
