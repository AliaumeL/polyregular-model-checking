{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Interpretation where

import Logic.Formulas
import QuantifierFree
import Logic.ProgramFormula (computeUntil)
import qualified Logic.ProgramFormula as PF
import qualified SimpleForPrograms as SFP
import SimpleForPrograms (Movement(..))

import Data.Map (Map)
import qualified Data.Map as M


data Interpretation tag = Interpretation {
    tags         :: [tag],
    alphabet     :: String,
    domain       :: tag -> [Var] -> Formula tag,
    order        :: tag -> tag   -> [Var] -> [Var] -> Formula tag,
    labelOrCopy  :: tag -> Either Char Int,
    arity        :: tag -> Int
}

maxArity :: Interpretation tag -> Int
maxArity interp = maximum $ map (arity interp) $ tags interp

stringify :: (tag -> String) -> Interpretation tag -> Interpretation String
stringify η (Interpretation τ sig δ ο λ α) = Interpretation τ1 sig δ1 ο1 λ1 α1
    where
        τ1 = [ η t | t <- τ ]

        mstrs = M.fromList $ zip τ1 τ

        δ1 s vs = mapTags η $ δ (mstrs M.! s) vs
        ο1 s1 s2 vs1 vs2 = mapTags η $ ο (mstrs M.! s1) (mstrs M.! s2) vs1 vs2
        λ1 s = λ (mstrs M.! s)
        α1 s = α (mstrs M.! s)

normalizeMovement :: Movement -> Movement
normalizeMovement (MoveIfL _) = MoveSeq 0
normalizeMovement (MoveIfR _) = MoveSeq 1
normalizeMovement (MoveSeq n) = MoveSeq n
normalizeMovement (MoveFor p d b) = MoveFor p d b

normalizeMovements :: [Movement] -> [Movement]
normalizeMovements = map normalizeMovement

-- whether "x" `happensBefore` "y"
happensBefore :: [Movement] -> [Movement] -> [Var] -> [Var] -> Formula ()
happensBefore [] [] _ _  = FConst True
happensBefore (MoveSeq i : ms) (MoveSeq j : ns) vm vn
    | i < j = FConst True
    | i > j = FConst False
    | otherwise = happensBefore ms ns vm vn
happensBefore (MoveFor _ SFP.LeftToRight _ : ms) (MoveFor _ SFP.LeftToRight _ : ns) (vm : vms) (vn : vns) = 
    andList [FTestPos Le vm vn, happensBefore ms ns vms vns]
happensBefore (MoveFor _ SFP.RightToLeft _ : ms) (MoveFor _ SFP.RightToLeft _ : ns) (vm : vms) (vn : vns) =
    andList [FTestPos Ge vm vn, happensBefore ms ns vms vns]
happensBefore _ _ _ _ = error $ "happensBefore: incompatible movements"


labelFormula :: SFP.ForProgram -> SFP.Path -> Either Char Int
labelFormula prog path = case stmt of 
                            SFP.PrintPos v -> Right $ vnum v path
                            SFP.PrintLbl c -> Left c
                            _          -> error "invalid stmt"
    where
        stmt = SFP.followPathProg path prog
        vars = SFP.pathPVars path

        vnumrec n _ [] = error "variable not found"
        vnumrec n i (x : xs) = if x == n then i else vnumrec n (i+1) xs

        vnum :: SFP.PName -> SFP.Path -> Int
        vnum n (SFP.Path p) = vnumrec n 0 (reverse vars)

toInterpretation :: SFP.ForProgram -> Interpretation SFP.Path
toInterpretation prog = Interpretation tags alphabet domain order labelOrCopy arity
    where
        -- print positions
        tags = SFP.listPrintStatements prog
        -- all characters in the program
        alphabet = SFP.listAlphabet prog
        -- print statements
        labelOrCopy = \tag -> labelFormula prog tag 
        -- domain formula => compute until + exists
        domain = \tag vars -> injectTags $ PF.formula $ PF.computeUntilProg tag prog
        -- order formula -> happens before
        order = \(SFP.Path p1) (SFP.Path p2) vars1 vars2 -> injectTags $ happensBefore p1 p2 vars1 vars2
        -- arities
        arity = length . SFP.pathPVars

