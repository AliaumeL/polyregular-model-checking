module Logic.PullBack where


import Logic.Formulas
import Logic.Interpretation

-- [∃x. φ] -> ∃x_t : Tag. ∃x_1, ..., x_n : Pos. [φ]
-- [φ ∨ ψ] -> [φ] ∨ [ψ]
-- [φ ∧ ψ] -> [φ] ∧ [ψ]
-- [φ ⇒ ψ] -> [φ] ⇒ [ψ]
-- [φ ⇔ ψ] -> [φ] ⇔ [ψ]
-- [¬φ] -> ¬[φ]
-- [ a(x)   ] -> /\_{t in Tags} (x_t = t => labelFormula ’a’ t x_1 ... x_arity(t))
-- [ x = y  ] -> \/_{t in Tags} x_t = y_t = t /\ x_1 = y_1 /\ ... /\ x_arity(t) = y_arity(t)
-- [ x <= y ] -> \/_{t in Tags} x_t = y_t = t /\ (orderFormula x_t y_t xi yi)
-- [ x <  y ] = [ x <= y ] ∧ [ x ≠ y ]
-- [ x >= y ] = [ x <= y ]
-- [ x >  y ] = [ x <  y ]
-- [ x ≠  y ] = ¬[ x = y ]
-- [ x has type t  ] = error
-- [ x is real pos ] = error
-- [ x pred pos    ] = error
pullBack :: Interpretation tag -> Formula () -> Formula tag
pullBack (Interpretation tags alph dom ord lab cop ar mar) φ = pb φ
    where
        pb (FConst True) = FConst True
        pb (FConst False) = FConst False
        pb (FVar x) = FVar x
        pb (FBin op left right) = FBin op (pb left) (pb right)
        pb (FNot inner) = FNot (pb inner)
        pb (FTestPos op x y) = undefined 
        pb (FLetter x letter) = undefined
        pb (FQuant Exists _ s inner) = undefined
        pb (FQuant Forall _ s inner) = undefined

        pb (FTag x tag) = error "pullBack: tag"
        pb (FPredPos p x) = error "pullBack: pred pos"
        pb (FRealPos x) = error "pullBack: real pos"
        



