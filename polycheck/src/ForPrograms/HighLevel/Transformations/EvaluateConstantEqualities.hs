{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.HighLevel.Transformations.EvaluateConstantEqualities (
    hasConstantEquality,
    removeConstantEquality
) where

import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing

-- | This module removes equality tests of the form
-- 'c' == 'd' where 'c' and 'd' are characters.
-- This is needed because simple for programs do not allow
-- for such comparisons, that can anyway be replaced 
-- by constants true/false.


hasConstantEquality :: Program String t -> Bool
hasConstantEquality (Program funcs _) = any hasConstantEqualityStmtFun funcs 
hasConstantEqualityStmtFun :: StmtFun String t -> Bool
hasConstantEqualityStmtFun (StmtFun _ _ stmt _) = hasConstantEqualityStmt stmt
hasConstantEqualityStmt :: Stmt String t -> Bool
hasConstantEqualityStmt (SYield o _) = hasConstantEqualityOExpr o
hasConstantEqualityStmt (SOReturn o _) = hasConstantEqualityOExpr o
hasConstantEqualityStmt (SBReturn b _) = hasConstantEqualityBExpr b
hasConstantEqualityStmt (SIf b s1 s2 _) = hasConstantEqualityBExpr b || hasConstantEqualityStmt s1 || hasConstantEqualityStmt s2
hasConstantEqualityStmt (SLetOutput _ o s _) = hasConstantEqualityOExpr o || hasConstantEqualityStmt s
hasConstantEqualityStmt (SLetBoolean _ s _) = hasConstantEqualityStmt s
hasConstantEqualityStmt (SSetTrue _ _) = False
hasConstantEqualityStmt (SFor _ _ v s _) = hasConstantEqualityOExpr v || hasConstantEqualityStmt s
hasConstantEqualityStmt (SSeq ss _) = any hasConstantEqualityStmt ss
hasConstantEqualityBExpr :: BExpr String t -> Bool
hasConstantEqualityBExpr (BLitEq _ (CChar _ _) (OConst (CChar _ _) _) _) = True
hasConstantEqualityBExpr (BLitEq _ _ _ _) = False
hasConstantEqualityBExpr (BConst _ _) = False
hasConstantEqualityBExpr (BNot b _) = hasConstantEqualityBExpr b
hasConstantEqualityBExpr (BOp _ b1 b2 _) = hasConstantEqualityBExpr b1 || hasConstantEqualityBExpr b2
hasConstantEqualityBExpr (BComp _ p1 p2 _) = False
hasConstantEqualityBExpr (BVar _ _) = False
hasConstantEqualityBExpr (BGen s _) = hasConstantEqualityStmt s
hasConstantEqualityBExpr (BApp _ oes _) = any hasConstantEqualityOExpr . map fst $ oes
hasConstantEqualityOExpr :: OExpr String t -> Bool
hasConstantEqualityOExpr (OVar _ _) = False
hasConstantEqualityOExpr (OConst (CChar _ _) _) = True
hasConstantEqualityOExpr (OConst _ _) = False
hasConstantEqualityOExpr (OList os _) = any hasConstantEqualityOExpr os
hasConstantEqualityOExpr (OApp _ oes _) = any hasConstantEqualityOExpr . map fst $ oes
hasConstantEqualityOExpr (OGen s _) = hasConstantEqualityStmt s



removeConstantEquality :: Program String t -> Program String t
removeConstantEquality (Program funcs main) = Program (map removeConstantEqualityStmtFun funcs) main
removeConstantEqualityStmtFun :: StmtFun String t -> StmtFun String t
removeConstantEqualityStmtFun (StmtFun name args stmt t) = StmtFun name args (removeConstantEqualityStmt stmt) t
removeConstantEqualityStmt :: Stmt String t -> Stmt String t
removeConstantEqualityStmt (SYield o t) = SYield (removeConstantEqualityOExpr o) t
removeConstantEqualityStmt (SOReturn o t) = SOReturn (removeConstantEqualityOExpr o) t
removeConstantEqualityStmt (SBReturn b t) = SBReturn (removeConstantEqualityBExpr b) t
removeConstantEqualityStmt (SIf b s1 s2 t) = SIf (removeConstantEqualityBExpr b) (removeConstantEqualityStmt s1) (removeConstantEqualityStmt s2) t
removeConstantEqualityStmt (SLetOutput (v, t1) e s t2) = SLetOutput (v, t1) (removeConstantEqualityOExpr e) (removeConstantEqualityStmt s) t2
removeConstantEqualityStmt (SLetBoolean b s t) = SLetBoolean b (removeConstantEqualityStmt s) t
removeConstantEqualityStmt (SSetTrue v t) = SSetTrue v t
removeConstantEqualityStmt (SFor dir v oes s t) = SFor dir v (removeConstantEqualityOExpr oes) (removeConstantEqualityStmt s) t
removeConstantEqualityStmt (SSeq ss t) = SSeq (map removeConstantEqualityStmt ss) t
removeConstantEqualityBExpr :: BExpr String t -> BExpr String t
removeConstantEqualityBExpr (BLitEq t (CChar c v) (OConst (CChar c' v') t'') t') 
    | c == c' = BConst True t'
    | otherwise = BConst False t'
removeConstantEqualityBExpr x@(BLitEq _ _ _ _) = x
removeConstantEqualityBExpr (BConst b t) = BConst b t
removeConstantEqualityBExpr (BNot b t) = BNot (removeConstantEqualityBExpr b) t
removeConstantEqualityBExpr (BOp op b1 b2 t) = BOp op (removeConstantEqualityBExpr b1) (removeConstantEqualityBExpr b2) t
removeConstantEqualityBExpr (BComp comp p1 p2 t) = BComp comp p1 p2 t
removeConstantEqualityBExpr (BVar v t) = BVar v t
removeConstantEqualityBExpr (BGen s t) = BGen (removeConstantEqualityStmt s) t
removeConstantEqualityBExpr (BApp v oes t) = BApp v (map (\(o, t') -> (removeConstantEqualityOExpr o, t')) oes) t
removeConstantEqualityOExpr :: OExpr String t -> OExpr String t
removeConstantEqualityOExpr (OVar v t) = OVar v t
removeConstantEqualityOExpr (OConst (CChar c t') t) = OConst (CChar c t') t
removeConstantEqualityOExpr (OConst c t) = OGen (SSeq [] t) t  -- Replace with an empty sequence
removeConstantEqualityOExpr (OList os t) = OList (map removeConstantEqualityOExpr os) t
removeConstantEqualityOExpr (OApp v oes t) = OApp v (map (\(o, t') -> (removeConstantEqualityOExpr o, t')) oes) t
removeConstantEqualityOExpr (OGen s t) = OGen (removeConstantEqualityStmt s) t


