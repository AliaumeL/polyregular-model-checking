module LiteralElimination where

-- This module is made to ensure that
-- every expression that is iterated over in a
-- for program is either
-- 1. a generator expression
-- 2. a variable
-- 3. the reverse of one of the above
-- 
-- This is a prerequisite for
-- our conversion to the "simple for program" case.


import ForPrograms
import ForProgramsTyping

eliminateLiterals :: Program String ValueType -> Program String ValueType
eliminateLiterals (Program funcs main) = Program (map eliminateLiteralFun funcs) main

eliminateLiteralFun :: StmtFun String ValueType -> StmtFun String ValueType
eliminateLiteralFun (StmtFun name args stmt t) = StmtFun name args (eliminateLiteralStmt stmt) t

eliminateLiteralBExpr :: BExpr String ValueType -> BExpr String ValueType
eliminateLiteralBExpr (BConst b t) = BConst b t
eliminateLiteralBExpr (BNot b t) = BNot (eliminateLiteralBExpr b) t
eliminateLiteralBExpr (BOp op b1 b2 t) = BOp op (eliminateLiteralBExpr b1) (eliminateLiteralBExpr b2) t
eliminateLiteralBExpr (BComp comp p1 p2 t) = BComp comp (eliminateLiteralPExpr p1) (eliminateLiteralPExpr p2) t
eliminateLiteralBExpr (BVar v t) = BVar v t
eliminateLiteralBExpr (BGen s t) = BGen (eliminateLiteralStmt s) t
eliminateLiteralBExpr (BApp _ _ _) = error "BApp in eliminateLiteralBExpr"
eliminateLiteralBExpr (BLitEq t (CChar c v) (OVar u tu) t') = BLitEq t (CChar c v) (OVar u tu) t'
eliminateLiteralBExpr (BLitEq t (CChar c v) (OConst (CChar c' v') t') t'') = BConst (c == c') t''
eliminateLiteralBExpr (BLitEq t (CChar c v) _ _) = BConst False t
eliminateLiteralBExpr (BLitEq t _ _ _) = error "BLitEq with non-char CExpr"

eliminateLiteralPExpr :: PExpr String ValueType -> PExpr String ValueType
eliminateLiteralPExpr (PVar v t) = PVar v t 

-- Convert a constant expression to a statement that produces
-- the same value
eliminateLiteralCExpr :: CExpr String ValueType -> Stmt String ValueType
eliminateLiteralCExpr c@(CChar _ _) = error $ "CChar in eliminateLiteralCExpr"
eliminateLiteralCExpr (CList [] t) = SSeq [] t
eliminateLiteralCExpr (CList cs ts@(TOutput (TOList TOChar))) = SSeq (map eliminateSubExpr cs) ts
    where
        eliminateSubExpr :: CExpr String ValueType -> Stmt String ValueType
        eliminateSubExpr c = SYield (OConst c (TOutput TOChar)) ts
eliminateLiteralCExpr (CList cs ts@(TOutput (TOList (TOList t)))) = SSeq (map eliminateSubExpr cs) ts
    where
        eliminateSubExpr :: CExpr String ValueType -> Stmt String ValueType
        eliminateSubExpr c = SYield (OGen (eliminateLiteralCExpr c) (TOutput t)) ts

eliminateLiteralOExpr :: OExpr String ValueType -> OExpr String ValueType
eliminateLiteralOExpr (OVar v t) = OVar v t 
eliminateLiteralOExpr (OConst (CChar c t') t) = OConst (CChar c t') t
eliminateLiteralOExpr (OConst (CList [] t') t) = OConst (CList [] t') t
eliminateLiteralOExpr (OConst c t) = OGen (eliminateLiteralCExpr c) t
eliminateLiteralOExpr (OList [] t) = OConst (CList [] t) t
eliminateLiteralOExpr (OList os t) = OGen (SSeq subexprs t) t
    where
        subexprs = do
            expr <- os
            return $ SYield (eliminateLiteralOExpr expr) t
eliminateLiteralOExpr (OApp _ _ _) = error "OApp in eliminateLiteralOExpr"
eliminateLiteralOExpr (OGen s t) = OGen (eliminateLiteralStmt s) t


eliminateLiteralStmt :: Stmt String ValueType -> Stmt String ValueType
eliminateLiteralStmt (SIf b s1 s2 t) = SIf (eliminateLiteralBExpr b) (eliminateLiteralStmt s1) (eliminateLiteralStmt s2) t
eliminateLiteralStmt (SYield o t) = SYield (eliminateLiteralOExpr o) t
eliminateLiteralStmt (SOReturn o t) = SOReturn (eliminateLiteralOExpr o) t
eliminateLiteralStmt (SBReturn b t) =  SBReturn (eliminateLiteralBExpr b) t
eliminateLiteralStmt (SLetOutput (v, t1) e s t2) = SLetOutput (v, t1) (eliminateLiteralOExpr e) (eliminateLiteralStmt s) t2
eliminateLiteralStmt (SLetBoolean b s t)  = SLetBoolean b (eliminateLiteralStmt s) t
eliminateLiteralStmt (SSetTrue b t) = SSetTrue b t
eliminateLiteralStmt (SFor dir (i, e, t) v s t') = SFor dir (i, e, t) (eliminateLiteralOExpr v) (eliminateLiteralStmt s) t'
eliminateLiteralStmt (SSeq ss t) = SSeq (map eliminateLiteralStmt ss) t
