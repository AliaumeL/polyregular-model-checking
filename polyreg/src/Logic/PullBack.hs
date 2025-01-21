{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.PullBack where

import Control.Monad.Reader

import QuantifierFree
import Logic.Formulas
import Logic.Interpretation

import Debug.Trace


-- A position variable in the "pullback" is a 
-- tag variable + a list of position variables.
data VarExpansion = VarExpansion {
    varTag :: Var,
    varPos :: [Var]
} deriving (Eq,Show)

data PBState = PBState {
    varStack :: [VarExpansion]
} deriving (Eq,Show)


class (Monad m) => MonadPB m where
    withNewPosVar :: Quant -> String -> Int -> ([(String, Sort, Quant)] -> m a) -> m a
    getPosVar     :: Var -> m VarExpansion

newtype PBMonad a = PBMonad (Reader PBState a) deriving (Functor, Applicative, Monad, MonadReader PBState)

runPBMonad :: PBMonad a -> a
runPBMonad (PBMonad m) = runReader m (PBState [])

shiftVarStack :: Int -> [VarExpansion] -> [VarExpansion]
shiftVarStack n = map (\(VarExpansion x xs) -> VarExpansion (shiftVar n x) (map (shiftVar n) xs))

instance MonadPB PBMonad where
    withNewPosVar q x n f = do
        let tx  = Local n (x ++ "_t")
        let pxs = map (\i -> Local (n-i-1) (x ++ "_" ++ show i)) [0..(n-1)]
        let ex  = VarExpansion tx pxs
        let quants = ((x ++ "_t", Tag, q) : [(x ++ "_" ++ show i, Pos, q) | i <- [0..(n-1)]])
        local (\s -> s { varStack = ex : (shiftVarStack (n+1) (varStack s)) }) $ f quants
    getPosVar (In _) = error "getPosVar: input variable"
    getPosVar (Out _) = error "getPosVar: output variable"
    getPosVar (Local i _) = do
        v <- asks varStack
        return $ v !! i


-- testing whether two position variables are equal / less / greater etc
-- > guess tags
-- > call the corresponding order relation
testPosVarExp :: Interpretation tag -> TestOp -> VarExpansion -> VarExpansion -> Formula tag
testPosVarExp i Eq (VarExpansion tx xs) (VarExpansion ty ys) = 
    orList $ do
        t <- tags i
        return . andList $ (FTag tx t) : (FTag ty t) : [ FTestPos Eq xi yi | (xi,yi) <- take (arity i t) $ zip xs ys ]
testPosVarExp i Le (VarExpansion tx xs) (VarExpansion ty ys) =
    orList $ do 
        realTagX <- tags i
        realTagY <- tags i
        return . andList $ [FTag tx realTagX, FTag ty realTagY, order i realTagX realTagY xs ys]
testPosVarExp i Ge x y = testPosVarExp i Le y x
testPosVarExp i Lt x y = andList [testPosVarExp i Le x y, testPosVarExp i Neq x y]
testPosVarExp i Gt x y = testPosVarExp i Lt y x
testPosVarExp i Neq x y = FNot $ testPosVarExp i Eq x y


-- testing whether the letter at given position is a given character.
-- > guess tag
-- > check whether it is "copied" or "labelled" print
-- > in case "copied", test the corresponding letter on the variable
-- > in case "labelled", answer directly true/false
letterVarExp :: Interpretation tag -> Char -> VarExpansion -> Formula tag
letterVarExp i c (VarExpansion tx xs) = 
    orList $ do
        t <- tags i
        case (labelOrCopy i t) of
            Left  c2 -> return . andList $ [(FConst (c == c2)), FTag tx t]
            Right j  -> do
                let vindex = (arity i t) - j - 1
                return . andList $ [FLetter (xs !! vindex) c, FTag tx t]


areFakePositions :: [Var] -> Formula tag
areFakePositions vs = andList $ map (\v -> FNot $ FRealPos v) vs

areRealPositions :: [Var] -> Formula tag
areRealPositions vs = andList $ map (\v -> FRealPos v) vs

varExpInDomain :: Interpretation tag -> VarExpansion -> Formula tag
varExpInDomain i (VarExpansion tx xs) = 
    orList $ do
        t <- tags i
        return . andList $ [(FTag tx t), addRealPositions (domain i t (take (arity i t) xs)),
                           (areFakePositions (drop (arity i t) xs)),
                           (areRealPositions (take (arity i t) xs))]


pullBackM :: (MonadPB m) => Interpretation tag -> Formula () -> m (Formula tag)
pullBackM i (FTag x tag) = error "pullBackM: tag"
pullBackM i (FRealPos x) = error "pullBackM: real pos"
pullBackM i (FQuant _ _ Tag _) = error "pullBackM: quant tag"
pullBackM i (FQuant _ _ Boolean _) = error "pullBackM: quant bool"
pullBackM i (FConst x) = return $ FConst x
pullBackM i (FVar x) = return $ FVar x
pullBackM i (FBin op left right) = FBin op <$> (pullBackM i left) <*> (pullBackM i right)
pullBackM i (FNot inner) = FNot <$> (pullBackM i inner)
pullBackM i (FTestPos op x y) = do
    vx <- getPosVar x
    vy <- getPosVar y
    return $ testPosVarExp i op vx vy
pullBackM i (FLetter x letter) = do
    vx <- getPosVar x
    return $ letterVarExp i letter vx
pullBackM i (FQuant q x Pos φ) = do
    withNewPosVar q x (maxArity i) $ \qs -> do
        currentVar <- getPosVar (Local 0 x)
        let λ = varExpInDomain i currentVar
        ξ <- pullBackM i φ
        case q of
            Forall -> return $ quantifyList qs (FBin Impl λ ξ)
            Exists -> return $ quantifyList qs (FBin Conj λ ξ)



--
-- Note that we cannot pullBack *in/out* variables: this would
-- require a more complex type system.

-- [∃x. φ] -> ∃x_t : Tag. ∃x_1, ..., x_n : Pos. [φ]
-- [φ ∨ ψ] -> [φ] ∨ [ψ]
-- [φ ∧ ψ] -> [φ] ∧ [ψ]
-- [φ ⇒ ψ] -> [φ] ⇒ [ψ]
-- [φ ⇔ ψ] -> [φ] ⇔ [ψ]
-- [¬φ] -> ¬[φ]
-- [ a(x)   ] -> /\_{t in Tags} (x_t = t => labelFormula ’a’ t x_1 ... x_arity(t))
--  ----> plus copy formula
--  ----> and the tested positions are *real*, untested positions are not *real*
-- [ x = y  ] -> \/_{t in Tags} x_t = y_t = t /\ x_1 = y_1 /\ ... /\ x_arity(t) = y_arity(t)
--  ----> and the tested positions are *real*, untested positions are not *real*
-- [ x <= y ] -> \/_{t in Tags} x_t = y_t = t /\ (orderFormula x_t y_t xi yi)
--  ----> and the tested positions are *real*, untested positions are not *real*
-- [ x <  y ] = [ x <= y ] ∧ [ x ≠ y ]
-- [ x >= y ] = [ x <= y ]
-- [ x >  y ] = [ x <  y ]
-- [ x ≠  y ] = ¬[ x = y ]
-- [ x has type t  ] = error
-- [ x is real pos ] = error
-- [ x pred pos    ] = error
pullBack :: Interpretation tag -> Formula () -> Formula tag
pullBack i φ = runPBMonad $ pullBackM i φ
