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

eliminateLiterals :: Program v t -> Program v t
eliminateLiterals (Program funcs main) = Program (map eliminateLiteralFun funcs) main

eliminateLiteralFun :: StmtFun v t -> StmtFun v t
eliminateLiteralFun (StmtFun name args stmt t) = StmtFun name args (eliminateLiteralStmt stmt) t

eliminateLiteralBExpr :: BExpr v t -> BExpr v t
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

eliminateLiteralPExpr :: PExpr v t -> PExpr v t
eliminateLiteralPExpr (PVar v t ) = PVar v t

-- Convert a constant expression to a statement that produces
-- the same value
eliminateLiteralCExpr :: CExpr v t -> Stmt v t
eliminateLiteralCExpr (CChar _ _) = error $ "CChar in eliminateLiteralCExpr"
eliminateLiteralCExpr (CList cs t) = SSeq (map (\c -> SYield (OConst c t) t) cs) t

eliminateLiteralOExpr :: OExpr v t -> OExpr v t
eliminateLiteralOExpr (OVar v t) = OVar v t
eliminateLiteralOExpr (OConst (CChar c t') t) = error "OConst in eliminateLiteralOExpr"
eliminateLiteralOExpr (OConst c t) = OGen (eliminateLiteralCExpr c) t
eliminateLiteralOExpr (OList os t) = OGen (SSeq subexprs t) t
    where
        subexprs = do
            expr <- os
            return $ SYield (eliminateLiteralOExpr expr) t
eliminateLiteralOExpr (ORev o t) = ORev (eliminateLiteralOExpr o) t
eliminateLiteralOExpr (OIndex _ _ _) = error "OIndex in eliminateLiteralOExpr"
eliminateLiteralOExpr (OApp _ _ _) = error "OApp in eliminateLiteralOExpr"
eliminateLiteralOExpr (OGen s t) = OGen (eliminateLiteralStmt s) t


eliminateLiteralStmt :: Stmt v t -> Stmt v t
eliminateLiteralStmt (SIf b s1 s2 t) = SIf (eliminateLiteralBExpr b) (eliminateLiteralStmt s1) (eliminateLiteralStmt s2) t
eliminateLiteralStmt (SYield o t) = SYield o t
eliminateLiteralStmt (SOReturn o t) = error "SOReturn in eliminateLiteralStmt"
eliminateLiteralStmt (SBReturn b t) =  error "SBReturn in eliminateLiteralStmt"
eliminateLiteralStmt (SLetOutput _ _ _ _) = error "SLetOutput in eliminateLiteralStmt"
eliminateLiteralStmt (SLetBoolean b s t)  = SLetBoolean b (eliminateLiteralStmt s) t
eliminateLiteralStmt (SSetTrue b t) = SSetTrue b t
eliminateLiteralStmt (SFor (i, e, t) v s t') = SFor (i, e, t) (eliminateLiteralOExpr v) (eliminateLiteralStmt s) t'
eliminateLiteralStmt (SSeq ss t) = SSeq (map eliminateLiteralStmt ss) t
