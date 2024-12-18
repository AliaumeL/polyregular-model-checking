{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ThreeSortedFormulas where

import QuantifierFree

import Control.Monad.Reader
import Control.Monad.Extra (anyM, allM)

import SimpleForPrograms as SFP

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
    | FBin BinOp (Formula tag ) (Formula tag )
    -- Unary negation
    | FNot (Formula tag )
    -- Q x : T. φ. /!\ the "string" is only for debug purposes /!\
    | FQuant Quant String Sort (Formula tag )
    -- l(x)  (tag Variable x equals tag l)
    | FTag Var tag
    -- a(x)  (position Variable x has letter a)
    | FLetter Var Char
    -- Position tests (equality, <=, <, >, >=)
    | FTestPos TestOp Var Var
  deriving (Show, Eq, Ord)

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


-- | A formula seen as a morphism in the category of something
-- so that they can be composed.
data ProgramFormula tag  = ProgramFormula {
    -- | the formula recognizing the function
    formula    :: Formula tag ,
    -- | the input variables (with their sorts)
    inputVars  :: Map String Sort,
    -- | the output variables (with their sorts)
    outputVars :: Map String Sort
} deriving (Show, Eq)


ignoreOutputVarUnsafe :: String -> ProgramFormula tag  -> ProgramFormula tag 
ignoreOutputVarUnsafe x (ProgramFormula φ iφ oφ) = ProgramFormula φ' iφ' oφ'
    where
        s   = oφ M.! x
        φ'  = FQuant Exists x s $ quantOutVars f φ
        iφ' = iφ
        oφ' = M.delete x oφ
        f y = if x == y then Just (0, y) else Nothing

ignoreOutputVar :: String -> ProgramFormula tag  -> ProgramFormula tag
ignoreOutputVar x p@(ProgramFormula _ _ oφ) =  case M.lookup x oφ of
                                                    Just _  -> ignoreOutputVarUnsafe x p
                                                    Nothing -> p

ignoreOutputVars :: [String] -> ProgramFormula tag  -> ProgramFormula tag 
ignoreOutputVars xs φ = foldr ignoreOutputVar φ xs


withFalseInput :: String -> ProgramFormula tag  -> ProgramFormula tag 
withFalseInput x (ProgramFormula φ iφ oφ) = ProgramFormula φ' iφ' oφ
    where
        φ'  = substituteBooleanVar f φ
        f y = if y == In x then FConst False else FVar y
        iφ' = M.delete x iφ

withFalseInputs :: [String] -> ProgramFormula tag  -> ProgramFormula tag
withFalseInputs xs φ = foldr withFalseInput φ xs


instance Semigroup (ProgramFormula tag ) where
    (ProgramFormula φ iφ oφ) <> (ProgramFormula ψ iψ oψ) = ProgramFormula θ iθ oθ
        where
            commonVars :: Map String Sort
            commonVars = M.intersection oφ iψ

            commonVarsSorted :: [(String, Sort, Quant)]
            commonVarsSorted = do 
                (x, s) <- M.toList commonVars
                return (x, s, Exists)

            commonVarsQ :: Map String Int
            commonVarsQ = M.fromList $ zip (map (\(x,_,_) -> x) commonVarsSorted) [0..]

            erasedVars :: Map String Sort
            erasedVars = (oψ `M.intersection` oφ) `M.difference` iψ

            iθ :: Map String Sort
            iθ = iφ `M.union` (iψ `M.difference` commonVars)

            oθ :: Map String Sort
            oθ = oψ `M.union` (oφ `M.difference` commonVars)

            (ProgramFormula φ' _ _) = ignoreOutputVars (M.keys erasedVars)
                                                       (ProgramFormula φ iφ oφ)

            ψ' = ψ

            fφ :: String -> Maybe (Int, String)
            fφ x = case M.lookup x commonVarsQ of
                        Just i   -> Just (i, x)
                        Nothing  -> Nothing

            fψ :: String -> Maybe (Int, String)
            fψ = fφ

            φ'' = quantOutVars fφ φ'

            ψ'' = quantInVars  fψ ψ'

            θ = quantifyList commonVarsSorted $ andList [φ'', ψ'']

instance Monoid (ProgramFormula tag ) where
    mempty = ProgramFormula (FConst True) M.empty M.empty


withNewBoolVar :: String -> ProgramFormula tag  -> ProgramFormula tag 
withNewBoolVar x p = ignoreOutputVar x $ withFalseInput x p

withNewBoolVars :: [String] -> ProgramFormula tag  -> ProgramFormula tag 
withNewBoolVars xs p = foldr withNewBoolVar p xs



setTrueBoolean :: String -> ProgramFormula tag 
setTrueBoolean x = ProgramFormula φ iφ oφ
    where
        φ  = FBin Equiv (FVar $ Out x) (FConst True)
        iφ = M.empty
        oφ = M.singleton x Boolean



boolExprToFormula :: SFP.BoolExpr -> Formula tag 
boolExprToFormula (SFP.BVar (BName v)) = FVar $ In v
boolExprToFormula (SFP.BConst b) = FConst b
boolExprToFormula (SFP.BNot e) = FNot $ boolExprToFormula e
boolExprToFormula (SFP.BBin op l r) = FBin op (boolExprToFormula l) (boolExprToFormula r)
boolExprToFormula (SFP.BTest op (PName x) (PName y)) = FTestPos op (In x) (In y)
boolExprToFormula (SFP.BLabelAt (PName x) t) = FLetter (In x) t


ifThenElse :: SFP.BoolExpr -> ProgramFormula tag  -> ProgramFormula tag  -> ProgramFormula tag 
ifThenElse b (ProgramFormula φ iφ oφ) (ProgramFormula ψ iψ oψ) = ProgramFormula ξ iξ oξ
    where
        θ = boolExprToFormula b

        totalOutputVars :: Map String Sort
        totalOutputVars = oφ `M.union` oψ

        missingOutputφ :: Map String Sort
        missingOutputφ = totalOutputVars `M.difference` oφ

        missingOutputψ :: Map String Sort
        missingOutputψ = totalOutputVars `M.difference` oψ

        identityMissingOutputφ :: Formula tag 
        identityMissingOutputφ = andList $ do 
            (x, s) <- M.toList missingOutputφ
            case s of 
                Boolean -> return $ FBin Equiv (FVar $ Out x) (FVar $ In x)
                _       -> error $ "ifThenElse: output variable " ++ x ++ " is not a boolean"

        identityMissingOutputψ :: Formula tag 
        identityMissingOutputψ = andList $ do 
            (x, s) <- M.toList missingOutputψ
            case s of 
                Boolean -> return $ FBin Equiv (FVar $ Out x) (FVar $ In x)
                _       -> error $ "ifThenElse: output variable " ++ x ++ " is not a boolean"
        
        ξ = orList [
                     andList [φ, identityMissingOutputφ, θ],
                     andList [ψ, identityMissingOutputψ, FNot θ ]
                   ]

        (iθ, _) = freeVars θ

        iξ = iφ `M.union` iψ `M.union` iθ

        oξ = totalOutputVars




iterOverVar :: String -> ProgramFormula tag  -> ProgramFormula tag
iterOverVar p (ProgramFormula φ iφ oφ) = ProgramFormula ξ iξ oξ
    where
        -- the number of output variables of φ, i.e., the ones
        -- that can actually *change* by computing φ
        unum :: Int
        unum = M.size oφ

        -- for every number 1 <= i <= unum
        -- we create a Position variable p_i
        iterPosVars :: [(Int, String, Sort)]
        iterPosVars = do
            i <- [1 .. unum]
            return (i, "p_" ++ show i, Pos)

        -- and variables "x_i" for all output variables x of φ
        iterUpdtVars :: [(Int, String, Sort)]
        iterUpdtVars = do
            i <- [1 .. (unum-1)]
            (x, s) <- M.toList oφ
            return (i, x, s)

        -- all quantified vars
        allVars :: [(Int, String, Sort)]
        allVars = iterUpdtVars ++ iterPosVars

        -- allVars as a map from (i, s) to the number of the quantified variable
        updtVarMap :: Map (Int, String) Int
        updtVarMap = M.fromList $ zip (map (\(i, x, _) -> (i, x)) iterUpdtVars) [0..]

        posVarMap  :: Map Int Int
        posVarMap  = M.fromList $ zip (map (\(i, _, _) -> i) iterPosVars) [length iterUpdtVars ..]

        -- finds the corresponding boolean variable
        -- for the variable x at iteration i
        getUpdtVar :: Int -> Int -> String -> Var 
        getUpdtVar 0    depth x = In x
        getUpdtVar n    depth x | n == unum = Out x
        getUpdtVar step depth x = case M.lookup (step, x) updtVarMap of
                                    Just i  -> Local (depth + i) x
                                    Nothing -> error $ "iterUntil: variable " ++ x ++ " not found"

        getPosVar :: Int -> Int -> String -> Var 
        getPosVar step depth x | x == p = case M.lookup step posVarMap of
                                            Just i  -> Local (depth + i) x
                                            Nothing -> error $ "iterUntil: variable " ++ x ++ " not found"
        getPosVar step depth x = In x

        -- Now, we construct the formulas [φ_i] for 0 <= i <= unum - 1
        -- where φ_i is φ with input   variables (updtVarMap i)
        -- and                 output  variables (updtVarMap i+1)
        subφ i = mapInVars (getUpdtVar i) $ 
                    mapOutVars (getUpdtVar (i+1)) $ 
                        mapInVars (getPosVar (i+1)) φ

        correctφ = andList $ [ subφ i | i <- [0 .. unum - 1] ]

        condLessThan 0 _ = FConst True
        condLessThan i x = FTestPos Gt x (Local (1 + (posVarMap M.! i)) p)

        condGreaterThan n _ | n == unum + 1 = FConst True
        condGreaterThan i x = FTestPos Lt x (Local (1 + (posVarMap M.! i)) p)
        
        quantifyIntermediatePos i λ = quantifyList [("pj", Pos, Forall)] $
                mapInVars (\d x -> if x == p then Local d "pj" else In x) $ 
                    FBin Impl (andList [
                        condLessThan    i     (Local 0 "pj"),
                        condGreaterThan (i+1) (Local 0 "pj")
                    ]) λ

        completenessAtStep i = mapInVars (getUpdtVar i) . mapOutVars (getUpdtVar i) $ 
                                quantifyIntermediatePos i φ

        completeness = andList [ completenessAtStep i | i <- [0 .. unum] ]


        orderedPositions = andList $ do 
            i <- [1.. (unum - 1)]
            let pi = Local (posVarMap M.! i) p
            let pj = Local (posVarMap M.! (i+1)) p
            return $ FTestPos Le pi pj

        ξ = quantifyList (map (\(_,x,s) -> (x,s, Exists)) $ reverse allVars) $
               andList [correctφ, orderedPositions, completeness]

        iξ = M.delete p iφ
        oξ = oφ




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



sfpToProgramFormula :: SFP.ForProgram -> ProgramFormula ()
sfpToProgramFormula (SFP.ForProgram bs stmt) = withFalseInputs boolVars $ sfpStmtToProgramFormula stmt
    where 
        boolVars = [ x | BName x <- bs ]

sfpStmtToProgramFormula :: SFP.ForStmt -> ProgramFormula ()
sfpStmtToProgramFormula (SFP.SetTrue (BName x)) = setTrueBoolean x
sfpStmtToProgramFormula (SFP.If b s1 s2) = ifThenElse b (sfpStmtToProgramFormula s1) (sfpStmtToProgramFormula s2)
sfpStmtToProgramFormula (SFP.PrintPos _) = mempty
sfpStmtToProgramFormula (SFP.PrintLbl _) = mempty
sfpStmtToProgramFormula (SFP.Seq ss) = mconcat $ map sfpStmtToProgramFormula ss
sfpStmtToProgramFormula (SFP.For (PName p) LeftToRight bs stmt) = iterOverVar p subProgram
    where
        boolVars = [ x | BName x <- bs ]
        subProgram = withNewBoolVars boolVars $ sfpStmtToProgramFormula stmt
sfpStmtToProgramFormula (SFP.For _ _ _ _) = error $ "only forward loops are supported"


-- check if there is "a" in the input
verySimpleForProgram :: SFP.ForProgram
verySimpleForProgram = SFP.ForProgram [BName "seen_a"] $ 
    SFP.For (SFP.PName "i") SFP.LeftToRight [] $
        SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
               (SFP.SetTrue $ BName "seen_a")
               (SFP.Seq [])
        
verySimpleForProgramAA :: SFP.ForProgram
verySimpleForProgramAA  = SFP.ForProgram [BName "seen_a1", BName "seen_a2"] $ 
    SFP.For (SFP.PName "i") SFP.LeftToRight [] $
        SFP.Seq [
            SFP.If (SFP.BBin Conj (SFP.BLabelAt (SFP.PName "i") 'a') (SFP.BVar (BName "seen_a1")))
                   (SFP.SetTrue $ BName "seen_a2")
                   (SFP.Seq []),
            SFP.If (SFP.BLabelAt (SFP.PName "i") 'a')
                   (SFP.SetTrue $ BName "seen_a1")
                   (SFP.Seq [])
                ]
        
