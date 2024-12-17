module LetBoolsToTop(bringLetBoolsToTop) where 

import ForPrograms 

bringLetBoolsToTop :: Program s t -> Program s t
bringLetBoolsToTop (Program fs main) = Program (map bringLetBoolsToTopFun fs) main

bringLetBoolsToTopFun :: StmtFun s t -> StmtFun s t 
bringLetBoolsToTopFun (StmtFun n args s t) =
    let (s', vars) = bringLetBoolsToTopStmt s in
    let s'' = withVars vars s' in
    StmtFun n args s'' t

getLabel :: Stmt s t -> t
getLabel (SIf _ _ _ t) = t
getLabel (SYield _ t) = t
getLabel (SOReturn _ t) = t
getLabel (SBReturn _ t) = t
getLabel (SLetOutput _ _ _ t) = t
getLabel (SLetBoolean _ _ t) = t
getLabel (SSetTrue _ t) = t
getLabel (SFor _ _ _ _ t) = t
getLabel (SSeq _ t) = t


withVars :: [s] -> Stmt s t -> Stmt s t 
withVars [] s = s 
withVars (v : vs) s = SLetBoolean v (withVars vs s) (getLabel s)

bringLetBoolsToTopStmt :: Stmt s t -> (Stmt s t, [s])
bringLetBoolsToTopStmt (SIf b s1 s2 t) =
    let (s1', v1) = bringLetBoolsToTopStmt s1 in
    let (s2', v2) = bringLetBoolsToTopStmt s2 in
    let b' = bringLetBoolsToTopBExpr b in
    (SIf b' s1' s2' t, v1 ++ v2)
bringLetBoolsToTopStmt (SYield e t) =
    let e' = bringLetBoolsToTopOExpr e in
    (SYield e' t, [])
bringLetBoolsToTopStmt (SOReturn e t) =
    let e' = bringLetBoolsToTopOExpr e in
    (SOReturn e' t, [])
bringLetBoolsToTopStmt (SBReturn b t) = 
    let b' = bringLetBoolsToTopBExpr b in
    (SBReturn b' t, [])
bringLetBoolsToTopStmt (SLetOutput n e s t) =
    let (s', v) = bringLetBoolsToTopStmt s in
    let e' = bringLetBoolsToTopOExpr e in
    (SLetOutput n e' s' t, v)
bringLetBoolsToTopStmt (SLetBoolean n s t) =
    let (s',  v) = bringLetBoolsToTopStmt s in
    (s', n : v)
bringLetBoolsToTopStmt s@(SSetTrue n t) = 
    (s, [])
bringLetBoolsToTopStmt (SSeq ss t) = 
    let ans = map bringLetBoolsToTopStmt ss in
    let s' = SSeq (map fst ans) t in
    let vs = concat $ map snd ans in
    (s', vs) 
bringLetBoolsToTopStmt (SFor d (i, v, ti) e s t) =
    let (s', vars) = bringLetBoolsToTopStmt s in
    let s'' = withVars vars s' in
    let e' = bringLetBoolsToTopOExpr e in
    (SFor d (i, v, ti) e' s'' t, [])

bringLetBoolsToTopOExpr :: OExpr s t -> OExpr s t
bringLetBoolsToTopOExpr e@(OVar _ _) = e
bringLetBoolsToTopOExpr e@(OConst _ _) = e
bringLetBoolsToTopOExpr (OList es t) =
    OList (map bringLetBoolsToTopOExpr es) t
bringLetBoolsToTopOExpr (OApp f args t) =
    let args' = map (\(e, ps) -> (bringLetBoolsToTopOExpr e, ps)) args in
    OApp f args' t
bringLetBoolsToTopOExpr (OGen stmt t) = 
    let (stmt', vs) = bringLetBoolsToTopStmt stmt in
    let stmt'' = withVars vs stmt' in
    OGen stmt'' t

bringLetBoolsToTopBExpr :: BExpr s t -> BExpr s t
bringLetBoolsToTopBExpr e@(BConst _ _) = e
bringLetBoolsToTopBExpr (BNot b t) = BNot (bringLetBoolsToTopBExpr b) t
bringLetBoolsToTopBExpr (BOp op b1 b2 t) = BOp op (bringLetBoolsToTopBExpr b1) (bringLetBoolsToTopBExpr b2) t
bringLetBoolsToTopBExpr e@(BComp _ e1 e2 _) = e
bringLetBoolsToTopBExpr e@(BVar _ _) = e
bringLetBoolsToTopBExpr (BApp f args t) =
    let args' = map (\(e, ps) -> (bringLetBoolsToTopOExpr e, ps)) args in
    BApp f args' t
bringLetBoolsToTopBExpr (BLitEq t c e tb) =
    let e' = bringLetBoolsToTopOExpr e in
    BLitEq t c e' tb
bringLetBoolsToTopBExpr (BGen stmt t) =
    let (stmt', vs) = bringLetBoolsToTopStmt stmt in
    let stmt'' = withVars vs stmt' in
    BGen stmt'' t
