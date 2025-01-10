{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.PullBack where

import Control.Monad.Reader

import QuantifierFree
import Logic.Formulas
import Logic.Interpretation


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

instance MonadPB PBMonad where
    withNewPosVar q x n f = do
        let tx  = Local n (x ++ "_t")
        let pxs = map (\i -> Local i (x ++ "_" ++ show i)) [0..(n-1)]
        let ex  = VarExpansion tx pxs
        let quants = ((x ++ "_t", Tag, q) : [(x ++ "_" ++ show i, Pos, q) | i <- [0..(n-1)]])
        local (\s -> s { varStack = ex : varStack s }) $ f quants
    getPosVar (In _) = error "getPosVar: input variable"
    getPosVar (Out _) = error "getPosVar: output variable"
    getPosVar (Local i _) = do
        v <- asks varStack
        return $ v !! i


-- testing whether two position variables are equal / less / greater etc
-- > guess tags
-- > call the corresponding order relation
testPosVarExp :: Interpretation String -> TestOp -> VarExpansion -> VarExpansion -> Formula String
testPosVarExp i Eq (VarExpansion tx xs) (VarExpansion ty ys) = 
    orList $ do
        t <- tags i
        return . andList $ (FTag tx t) : (FTag ty t) : [ FTestPos Eq xi yi | (xi,yi) <- take (arity i t) $ zip xs ys ]
testPosVarExp i Le (VarExpansion tx xs) (VarExpansion ty ys) =
    orList $ do 
        realTagX <- tags i
        realTagY <- tags i
        return . andList $ [FTag tx realTagX, FTag ty realTagY, order i realTagX realTagY xs ys]
testPosVar i Ge x y = testPosVar i Le y x
testPosVar i Lt x y = andList [testPosVar i Le x y, testPosVar i Neq x y]
testPosVar i Gt x y = testPosVar i Lt y x
testPosVar i Neq x y = FNot $ testPosVar i Eq x y


-- testing whether the letter at given position is a given character.
-- > guess tag
-- > check whether it is "copied" or "labelled" print
-- > in case "copied", test the corresponding letter on the variable
-- > in case "labelled", answer directly true/false
letterVarExp :: Interpretation String -> Char -> VarExpansion -> Formula String
letterVarExp i c (VarExpansion tx xs) = 
    orList $ do
        t <- tags i
        case (labelOrCopy i t) of
            Left  c2 -> return . andList $ [(FConst (c == c2)), FTag tx t]
            Right j  -> return  . andList $ [FLetter (xs !! j) c, FTag tx t]



pullBackM :: (MonadPB m) => Interpretation String -> Formula () -> m (Formula String)
pullBackM i (FTag x tag) = error "pullBackM: tag"
pullBackM i (FPredPos p x) = error "pullBackM: pred pos"
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
        ξ <- pullBackM i φ
        return $ quantifyList qs ξ



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
pullBack = undefined
