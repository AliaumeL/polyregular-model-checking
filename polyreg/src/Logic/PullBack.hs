module Logic.PullBack where


import Logic.Formulas
import Logic.Interpretation


-- TODO: create a monad
-- with a state (stack) that keeps track of what "tuple of variables"
-- is associated to an old variable.
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
pullBack (Interpretation tags alph dom ord labCop ar) φ = pb φ
    where
        pb (FConst True) = FConst True
        pb (FConst False) = FConst False
        pb (FVar x) = FVar x
        pb (FBin op left right) = FBin op (pb left) (pb right)
        pb (FNot inner) = FNot (pb inner)
        -- [ x `op` y ] ->
        -- \/_{t in Tags} (x_t = t /\ y_t = t /\ ...)
        pb (FTestPos op x y) = undefined {- do
            (tx, xs) <- getPosVar x
            (ty, ys) <- getPosVar y
            return $ undefined -}
        pb (FLetter x letter) = undefined
        -- [∃x. φ] -> ∃x_t : Tag. ∃x_1, ..., x_n : Pos. [φ]
        -- and in [φ] we know that variable x maps to (x_t, x_1, ..., x_n)
        pb (FQuant Exists _ s inner) = undefined
        -- [∀x. φ] -> ∀x_t : Tag. ∀x_1, ..., x_n : Pos. [φ]
        -- and in [φ] we know that variable x maps to (x_t, x_1, ..., x_n)
        pb (FQuant Forall _ s inner) = undefined

        pb (FTag x tag) = error "pullBack: tag"
        pb (FPredPos p x) = error "pullBack: pred pos"
        pb (FRealPos x) = error "pullBack: real pos"
        



