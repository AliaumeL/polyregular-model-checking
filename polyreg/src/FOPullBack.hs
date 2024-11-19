module FOPullBack where

-- This module pulls back a first-order formula 
-- through an FO interpretation.

import TwoSortedFormulas (Formula)
import QuantifierFree
import qualified TwoSortedFormulas as TSF
import qualified FOInterpretation as FOI
import FOInterpretation (FOInterpretation(..))

type PosVarName = String
type TagVarName = String

-- We also want to be able to inject directly FOI.Formula into TSF.Formula.

inject :: FOI.Formula PosVarName alphabet -> Formula tag alphabet
inject FOI.FOTrue = TSF.FTrue
inject FOI.FOFalse = TSF.FFalse
inject (FOI.FOTestPos t x y) = TSF.FTestPos t x y
inject (FOI.FOCharAt x a) = TSF.FLetter x a
inject (FOI.FONot f) = TSF.FNot (inject f)
inject (FOI.FOBin op f g) = TSF.FBin op (inject f) (inject g)
inject (FOI.FOQuant FOI.Exists x f) = TSF.FQuant TSF.Exists x TSF.Pos (inject f)
inject (FOI.FOQuant FOI.Forall x f) = TSF.FQuant TSF.Forall x TSF.Pos (inject f)

-- The semantics is:
--
-- [ φ `bin` ψ ] = [φ] `bin` [ψ]
-- [ ¬φ ] = ¬[φ]
-- [ Q x. φ ] = Q xT : Tag. Q x1,...,xn : Pos. GuardI (xT, x1, …, xn) ( => / /\ ) [φ]
-- [ a(x) ]   = \/ (xT = t1 /\ I_{t1,a} (x1,..., xn))
-- [ x <= y ]  = \/ (xT = t1 /\ yT = t2 /\ I_(t1,t2) (x1,..., xn, y1,..., yn))
-- [ x = y  ]  = xT = yT /\ x1 = y1 /\ ... /\ xn = yn

class (Monad m) => MonadPullBack m where
    freshVar :: FOI.VarName -> m (TagVarName, [PosVarName])
    getPos   :: FOI.VarName -> m (TagVarName, [PosVarName])


pullBack :: (MonadPullBack m) => 
            FOI.FOInterpretation PosVarName alphabet tag ->
            FOI.Formula PosVarName alphabet -> 
            m (Formula tag alphabet)
pullBack _ FOI.FOTrue = return TSF.FTrue
pullBack _ FOI.FOFalse = return TSF.FFalse
-- position comparison (using the interpretation)
pullBack i (FOI.FOTestPos Eq x y)  = do
    -- get variable names
    (t1, xs) <- getPos x
    (t2, ys) <- getPos y
    -- guess a tag name
    let disjuncts = do
                        t <- tags i
                        -- assert that the tags match
                        let xt = TSF.FTag t1 t
                        let yt = TSF.FTag t2 t
                        -- assert that the positions match *up to the tag arity*
                        let xypos = TSF.andList . take (arity i t) $ zipWith (TSF.FTestPos Eq) xs ys
                        return . TSF.andList $ [xt, yt, xypos]
    return . TSF.orList $ disjuncts
-- position comparison (using the interpretation)
pullBack i (FOI.FOTestPos Le x y) = do
    -- get variable names
    (t1, xs) <- getPos x
    (t2, ys) <- getPos y
    -- guess a tag name for both
    let disjuncts = do
                        tx <- tags i
                        ty <- tags i
                        -- assert that the tags match
                        let xt = TSF.FTag t1 tx
                        let yt = TSF.FTag t2 ty
                        -- Create the formula
                        let phi = orderFormula i tx ty (take (arity i tx) xs) (take (arity i ty) ys)
                        return . TSF.andList $ [xt, yt, inject phi]
    return . TSF.orList $ disjuncts
pullBack i (FOI.FOTestPos Lt x y) = do
    -- get formula for <= 
    phi <- pullBack i (FOI.FOTestPos Le x y)
    -- get formula for equality
    psi <- pullBack i (FOI.FOTestPos Eq x y)
    -- return phi /\ not psi
    return $ TSF.FBin Conj phi (TSF.FNot psi)
pullBack i (FOI.FOTestPos Gt x y) = pullBack i (FOI.FOTestPos Lt y x)
pullBack i (FOI.FOTestPos Ge x y) = pullBack i (FOI.FOTestPos Le y x)
-- character comparison
pullBack i (FOI.FOCharAt x a) = do
    -- get variable names
    (t, xs) <- getPos x
    -- guess a tag name
    let disjuncts = do
                        tx <- tags i
                        -- assert that the tags match
                        let xt = TSF.FTag t tx
                        let phi = labelFormula i tx a (take (arity i tx) xs)
                        return . TSF.andList $ [xt, inject phi]
    return . TSF.orList $ disjuncts
-- negation
pullBack i (FOI.FONot f) = TSF.FNot <$> (pullBack i f)
-- binary operators
pullBack i (FOI.FOBin op f g) = TSF.FBin op <$> (pullBack i f) <*> (pullBack i g)
-- quantifiers
pullBack i (FOI.FOQuant FOI.Exists x f) = do
    -- get variable names
    (t, xs) <- freshVar x
    -- guess a tag name
    let disjuncts = do
                        tx <- tags i
                        -- assert that the tags match
                        let xt = TSF.FTag t tx
                        -- Create the formula
                        let phi = domainFormula i tx (take (arity i tx) xs)
                        return . TSF.andList $ [xt, inject phi]
    -- Quantify existentially over the tag t
    -- and all positions
    let quants :: [(String, TSF.Sort, TSF.Quant)]
        quants = [(t, TSF.Tag, TSF.Exists)] ++ [(x, TSF.Pos, TSF.Exists) | x <- xs]
    phi <- pullBack i f
    return . TSF.quantifyList quants $ TSF.FBin Conj (TSF.orList disjuncts) phi
pullBack i (FOI.FOQuant FOI.Forall x f) = do 
    -- get variable names
    (t, xs) <- freshVar x
    -- guess a tag name
    let disjuncts = do
                        tx <- tags i
                        -- assert that the tags match
                        let xt = TSF.FTag t tx
                        -- Create the formula
                        let phi = domainFormula i tx (take (arity i tx) xs)
                        return . TSF.andList $ [xt, inject phi]
    -- Quantify existentially over the tag t
    -- and all positions
    let quants :: [(String, TSF.Sort, TSF.Quant)]
        quants = [(t, TSF.Tag, TSF.Exists)] ++ [(x, TSF.Pos, TSF.Forall) | x <- xs]
    phi <- pullBack i f
    return . TSF.quantifyList quants $ TSF.FBin Impl (TSF.orList disjuncts) phi
