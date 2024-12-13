{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module BooleanElimination (hasBooleanGen, removeBooleanGen) where

import ForPrograms
import ForProgramsTyping

import Control.Monad.State

-- In this module, we try to remove *boolean generators*
-- from the AST.
--
-- We assume that
-- 1. there are no "BLitEq" except for chars
-- 2. there are no "BApp"
--


hasBooleanGen :: Program v t -> Bool
hasBooleanGen (Program funcs _) = any hasBooleanGenStmtFun funcs

hasBooleanGenStmtFun :: StmtFun v t -> Bool
hasBooleanGenStmtFun (StmtFun _ _ stmt _) = hasBooleanGenStmt stmt

hasBooleanGenStmt :: Stmt v t -> Bool
hasBooleanGenStmt (SYield o _) = hasBooleanGenOExpr o
hasBooleanGenStmt (SOReturn o _) = hasBooleanGenOExpr o
hasBooleanGenStmt (SBReturn b _) = hasBooleanGenBExpr b
hasBooleanGenStmt (SIf b s1 s2 _) = hasBooleanGenBExpr b || hasBooleanGenStmt s1 || hasBooleanGenStmt s2
hasBooleanGenStmt (SLetOutput _ o s _) = hasBooleanGenOExpr o || hasBooleanGenStmt s
hasBooleanGenStmt (SLetBoolean _ s _) = hasBooleanGenStmt s
hasBooleanGenStmt (SSetTrue _ _) = False
hasBooleanGenStmt (SFor _ _ v s _) = hasBooleanGenOExpr v || hasBooleanGenStmt s
hasBooleanGenStmt (SSeq ss _) = any hasBooleanGenStmt ss

hasBooleanGenOExpr :: OExpr v t -> Bool
hasBooleanGenOExpr (OVar _ _) = False
hasBooleanGenOExpr (OConst _ _) = False
hasBooleanGenOExpr (OList os _) = any hasBooleanGenOExpr os
hasBooleanGenOExpr (OApp _ os _) = any (hasBooleanGenOExpr . fst) os
hasBooleanGenOExpr (OGen s _) = hasBooleanGenStmt s

hasBooleanGenBExpr :: BExpr v t -> Bool
hasBooleanGenBExpr (BConst _ _) = False
hasBooleanGenBExpr (BNot b _) = hasBooleanGenBExpr b
hasBooleanGenBExpr (BOp _ b1 b2 _) = hasBooleanGenBExpr b1 || hasBooleanGenBExpr b2
hasBooleanGenBExpr (BComp _ _ _ _) = False
hasBooleanGenBExpr (BVar _ _) = False
hasBooleanGenBExpr (BGen _ _) = True
hasBooleanGenBExpr (BApp _ os _) = any (hasBooleanGenOExpr . fst) os
hasBooleanGenBExpr (BLitEq _ _ o _) = hasBooleanGenOExpr o


-- The only place where a boolean generator can appear
-- is in a boolean expression, which itself can only 
-- be the condition of an "IF" statement.
--
-- The rule is therefore of the form
--
-- if bexpr left right
-- -------------------
-- let b1,...,bk = False in (k is the number of boolean generators in the expression bexpr)
-- let r1,...,rk = False in 
-- Sequence all the si[ return x -> if not ri (setTrue ri; if x (SetTrue bi) () ) () ];
-- if bexpr[generator_i -> bi] left right
--
-- 
-- Step 1. collect all generators from a boolean expression
-- Step 2. create fresh variable names for the generators and their "return" variables
-- Step 3. substitute the returns by the nice "if" statement
-- Step 4. substitute the generators by the fresh variables in the bexpr
-- Step 5. introduce all variables, sequence all statements and the new if

class (Monad m) => MonadFresh m where
    fresh :: String -> m String


newtype FreshM a = FreshM (State Int a)
    deriving (Functor, Applicative, Monad)



-- replaceHashPart "a#..." 13 = "a#13"
-- replaceHashPart "abc" 123 = "abc#123"
replaceHashPart :: Int -> String -> String
replaceHashPart i s = case break (=='#') s of
    (a, '#':b) -> a ++ "#belim#" ++ show i
    (a, b)     -> a ++ "#belim#" ++ show i


instance MonadFresh FreshM where
    fresh s = FreshM $ do
        i <- get
        put (i + 1)
        return . replaceHashPart i $ s

runFreshM :: FreshM a -> a
runFreshM (FreshM m) = evalState m 0

-- extrats generators, together with two new variable names
-- (step 1/2/4)
extractFreshGenerators :: (MonadFresh m) => BExpr String ValueType -> m (BExpr String ValueType, [(Stmt String ValueType, String, String)])
extractFreshGenerators (BConst b t) = return (BConst b t, [])
extractFreshGenerators (BNot b t) = do
    (b', l) <- extractFreshGenerators b
    return (BNot b' t, l)
extractFreshGenerators (BOp op b1 b2 t) = do
    (b1', l1) <- extractFreshGenerators b1
    (b2', l2) <- extractFreshGenerators b2
    return (BOp op b1' b2' t, l1 ++ l2)
extractFreshGenerators (BComp comp p1 p2 t) = return (BComp comp p1 p2 t, [])
extractFreshGenerators (BVar v t) = return (BVar v t, [])
extractFreshGenerators (BGen s t) = do
    v <- fresh "gen"
    r <- fresh "ret"
    return (BVar v t, [(s, v, r)])
extractFreshGenerators (BApp _ _ _) = error "extractFreshGenerators: BApp is impossible"
extractFreshGenerators (BLitEq t c o t') = return (BLitEq t c o t', [])


returnWithVar :: ValueType -> String -> String -> BExpr String ValueType -> Stmt String ValueType
returnWithVar t b r x = SIf (BNot (BVar r TBool) TBool)
                          (SSeq [(SSetTrue r t), 
                                (SIf x (SSetTrue b t) (SSeq [] t) t)] t)
                          (SSeq [] t)
                          t

-- (step 3)
-- NOTE: we also need to change the *type* of the
-- statement, because now it is not doing anything (has any possible type),
-- and we actually want it to have a certain type
substituteReturnBool :: ValueType -> String -> String -> Stmt String ValueType -> Stmt String ValueType
substituteReturnBool t _ _ (SSetTrue v _) = SSetTrue v t
substituteReturnBool _ _ _ (SYield _ _) = error "substituteReturnBool: SYield is impossible"
substituteReturnBool _ _ _ (SOReturn _ _) = error "substituteReturnBool: SOReturn is impossible"
substituteReturnBool t b r (SBReturn x _) = returnWithVar t b r x
substituteReturnBool t b r (SIf b' s1 s2 _) = SIf b' (substituteReturnBool t b r s1) (substituteReturnBool t b r s2) t
substituteReturnBool t b r (SLetOutput v o s _) = SLetOutput v o (substituteReturnBool t b r s) t
substituteReturnBool t b r (SLetBoolean v s _) = SLetBoolean v (substituteReturnBool t b r s) t
substituteReturnBool t b r (SFor dir v o s _) = SFor dir v o (substituteReturnBool t b r s) t
substituteReturnBool t b r (SSeq ss _) = SSeq (map (substituteReturnBool t b r) ss) t

-- (step 5. a)
-- the type given should be the return type of the block /!\
introduceAllVariables :: ValueType -> [(Stmt String ValueType, String, String)] -> Stmt String ValueType -> Stmt String ValueType
introduceAllVariables t l block = letBooleans t boolAllVars $ SSeq allBlocks t
    where 
        boolOutputVars = map (\(_, b, _) -> b) l
        boolReturnVars = map (\(_, _, r) -> r) l
        boolAllVars = boolOutputVars ++ boolReturnVars
        generatorBlocks = map (\(s, b, r) -> substituteReturnBool t b r s) l
        allBlocks = generatorBlocks ++ [block]

-- (step 5. final)
removeIfGenerators :: (MonadFresh m) => ValueType -> BExpr String ValueType -> Stmt String ValueType -> Stmt String ValueType -> m (Stmt String ValueType)
removeIfGenerators t bexpr left right = do
    (bexpr', generators) <- extractFreshGenerators bexpr
    let newIf = SIf bexpr' left right t
    return $ introduceAllVariables t generators newIf


-- To remove boolean generators, we need to *inline* the generators
-- into the expressions where they are used.
-- This means recursively traversing the AST and replacing the
-- generators *bottom-up*. 

removeBooleanGen :: Program String ValueType -> Program String ValueType
removeBooleanGen p = runFreshM $ removeBooleanGenM p

removeBooleanGenM :: (MonadFresh m) =>  Program String ValueType -> m (Program String ValueType)
removeBooleanGenM (Program funcs m) = do
    funcs' <- mapM removeBooleanGenStmtFun funcs
    return $ Program funcs' m



removeBooleanGenStmtFun :: (MonadFresh m) =>  StmtFun String ValueType -> m (StmtFun String ValueType)
removeBooleanGenStmtFun (StmtFun name args stmt t) = do
    stmt' <- removeBooleanGenStmt stmt
    return $ StmtFun name args stmt' t

removeBooleanGenStmt :: (MonadFresh m) =>  Stmt String ValueType -> m (Stmt String ValueType)
removeBooleanGenStmt (SYield o t) = do
    o' <- removeBooleanGenOExpr o
    return $ SYield o' t
removeBooleanGenStmt (SOReturn o t) = do
    o' <- removeBooleanGenOExpr o
    return $ SOReturn o' t
removeBooleanGenStmt (SBReturn b t) = do
    b' <- removeBooleanGenBExpr b
    return $ SBReturn b' t
removeBooleanGenStmt (SIf b s1 s2 t) = do
    b' <- removeBooleanGenBExpr b
    s1' <- removeBooleanGenStmt s1
    s2' <- removeBooleanGenStmt s2
    removeIfGenerators t b' s1' s2'
removeBooleanGenStmt (SLetOutput v o s t) = do
    o' <- removeBooleanGenOExpr o
    s' <- removeBooleanGenStmt s
    return $ SLetOutput v o' s' t
removeBooleanGenStmt (SLetBoolean v s t) = do
    s' <- removeBooleanGenStmt s
    return $ SLetBoolean v s' t
removeBooleanGenStmt (SSetTrue v t) = return $ SSetTrue v t
removeBooleanGenStmt (SFor dir v o s t) = do
    o' <- removeBooleanGenOExpr o
    s' <- removeBooleanGenStmt s
    return $ SFor dir v o' s' t
removeBooleanGenStmt (SSeq ss t) = do
    ss' <- mapM (removeBooleanGenStmt) ss
    return $ SSeq ss' t

removeBooleanGenOExpr :: (MonadFresh m) =>  OExpr String ValueType -> m (OExpr String ValueType)
removeBooleanGenOExpr (OApp _ _ _) = error "removeBooleanGenOExpr: OApp is impossible"
removeBooleanGenOExpr (OVar v t) = return $ OVar v t
removeBooleanGenOExpr (OConst c t) = return $ OConst c t
removeBooleanGenOExpr (OList os t) = do
    os' <- mapM removeBooleanGenOExpr os
    return $ OList os' t
removeBooleanGenOExpr (OGen s t) = do
    s' <- removeBooleanGenStmt s
    return $ OGen s' t

removeBooleanGenBExpr :: (MonadFresh m) =>  BExpr String ValueType -> m (BExpr String ValueType)
removeBooleanGenBExpr (BConst b t) = return $ BConst b t
removeBooleanGenBExpr (BNot b t) = do
    b' <- removeBooleanGenBExpr b
    return $ BNot b' t
removeBooleanGenBExpr (BOp op b1 b2 t) = do
    b1' <- removeBooleanGenBExpr b1
    b2' <- removeBooleanGenBExpr b2
    return $ BOp op b1' b2' t
removeBooleanGenBExpr (BComp comp p1 p2 t) = return $ BComp comp p1 p2 t
removeBooleanGenBExpr (BVar v t) = return $ BVar v t
removeBooleanGenBExpr (BGen s t) = do
    s' <- removeBooleanGenStmt s
    return $ BGen s' t
removeBooleanGenBExpr (BApp _ _ _) = error "removeBooleanGenBExpr: BApp is impossible"
removeBooleanGenBExpr (BLitEq t' c o t) = do
    o' <- removeBooleanGenOExpr o
    return $ BLitEq t' c o' t
