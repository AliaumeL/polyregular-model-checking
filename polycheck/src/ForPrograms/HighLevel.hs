{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForPrograms.HighLevel where

import           Data.Set (Set, empty, singleton, union, unions)
import qualified Data.Set as S

import Logic.QuantifierFree

-- | we add a type parameter "t" for decorating the AST with types later on
data BExpr v t = BConst Bool t
               | BNot (BExpr v t) t
               | BOp BinOp (BExpr v t) (BExpr v t) t
               | BComp TestOp (PExpr v t) (PExpr v t) t
               | BVar v t
               | BGen (Stmt v t) t
               -- tests
               | BApp v [(OExpr v t, [PExpr v t])] t
               | BLitEq t (CExpr v t) (OExpr v t) t
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data PExpr v t = PVar v t
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data CExpr v t = CChar Char t
               | CList [CExpr v t] t
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Semigroup (CExpr v t) where
    CList xs t <> CList ys _ = CList (xs ++ ys) t
    _ <> _ = error "Cannot concatenate"

data OExpr v t = OVar v t
               | OConst (CExpr v t) t
               | OList [OExpr v t] t
               | OApp v [(OExpr v t, [PExpr v t])] t
               | OGen (Stmt v t) t -- generator expression
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Direction = Forward | Backward deriving (Show, Eq, Ord)

reverseDirection :: Direction -> Direction
reverseDirection Forward = Backward
reverseDirection Backward = Forward

-- For statements:
-- 1. Function declarations
-- 2. Block of statements
-- 3. A single statement
data Stmt v t = SIf (BExpr v t) (Stmt v t) (Stmt v t) t
              | SYield (OExpr v t) t
              | SOReturn (OExpr v t) t
              | SBReturn (BExpr v t) t
              | SLetOutput (v, t) (OExpr v t) (Stmt v t) t
              | SLetBoolean v (Stmt v t) t
              | SSetTrue v t
              | SFor Direction (v, v, t) (OExpr v t) (Stmt v t) t
              | SSeq [Stmt v t] t
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


programDepth :: Program v t -> Int
programDepth (Program [] _) = 0
programDepth (Program fs _) = maximum (map depthFun fs)
    where
        depthFun :: StmtFun v t -> Int
        depthFun (StmtFun _ args s _) = depthStmt s 0

        depthStmt :: Stmt v t -> Int -> Int
        depthStmt (SIf _ s1 s2 _) x = max (depthStmt s1 x) (depthStmt s2 x)
        depthStmt (SYield _ _) x = x
        depthStmt (SOReturn _ _) x = x
        depthStmt (SBReturn _ _) x = x
        depthStmt (SLetOutput _ _ s _) x = depthStmt s x
        depthStmt (SLetBoolean _ s _) x = depthStmt s x
        depthStmt (SSetTrue _ _) x = x
        depthStmt (SFor _ _ _ s _) x = depthStmt s (x + 1)
        depthStmt (SSeq [] _) x = x
        depthStmt (SSeq ss _) x = maximum (map (`depthStmt` x) ss)

programSize :: Program v t -> Int
programSize (Program fs _) = sum (map sizeFun fs)
    where
        sizeFun :: StmtFun v t -> Int
        sizeFun (StmtFun _ args s _) = sizeStmt s

        sizeStmt :: Stmt v t -> Int
        sizeStmt (SIf b s1 s2 _) = 1 + sizeBExpr b + sizeStmt s1 + sizeStmt s2
        sizeStmt (SYield _ _) = 1
        sizeStmt (SOReturn _ _) = 1
        sizeStmt (SBReturn _ _) = 1
        sizeStmt (SLetOutput _ o s _) = 1 + sizeStmt s + sizeOExpr o
        sizeStmt (SLetBoolean _ s _) = 1 + sizeStmt s
        sizeStmt (SSetTrue _ _) = 1
        sizeStmt (SSeq ss _) = sum (map sizeStmt ss)
        sizeStmt (SFor _ _ o s _) = 1 + sizeStmt s + sizeOExpr o

        sizeBExpr :: BExpr v t -> Int
        sizeBExpr (BConst _ _) = 0
        sizeBExpr (BNot b _) = sizeBExpr b
        sizeBExpr (BOp _ b1 b2 _) = sizeBExpr b1 + sizeBExpr b2
        sizeBExpr (BComp _ p1 p2 _) = 0
        sizeBExpr (BVar _ _) = 0
        sizeBExpr (BGen s _) = 1 + sizeStmt s
        sizeBExpr (BApp _ os _) = sum (map (sizeOExpr . fst) os)
        sizeBExpr (BLitEq _ c o _) = sizeOExpr o


        sizeOExpr :: OExpr v t -> Int
        sizeOExpr (OVar _ _) = 0
        sizeOExpr (OConst _ _) = 0
        sizeOExpr (OList os _) = sum (map sizeOExpr os)
        sizeOExpr (OApp _ os _) = sum (map (sizeOExpr . fst) os)
        sizeOExpr (OGen s _) = 1 + sizeStmt s






oExprType :: OExpr v t -> t
oExprType (OVar _ t) = t
oExprType (OConst _ t) = t
oExprType (OList _ t) = t
oExprType (OApp _ _ t) = t
oExprType (OGen _ t) = t


letBooleans :: t -> [String] -> Stmt String t -> Stmt String t
letBooleans _ [] block = block
letBooleans t [b] block = SLetBoolean b block t
letBooleans t (b : bs) block = SLetBoolean b (letBooleans t bs block) t

letOutputs :: t -> [(String, OExpr String t)] -> Stmt String t -> Stmt String t
letOutputs _ [] block = block
letOutputs t [(v, e)] block = SLetOutput (v, oExprType e) e block t
letOutputs t ((v, e) : es) block = SLetOutput (v, oExprType e) e (letOutputs t es block) t

-- | declares a function with a given type and a block of statements
data StmtFun v t = StmtFun v [(v, t, [v])] (Stmt v t) t
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

funName :: StmtFun v t -> v
funName (StmtFun v _ _ _) = v


-- | A program is a list of functions together with a "main" entrypoint
data Program v t = Program [StmtFun v t] v
    deriving (Show, Eq, Ord, Traversable, Functor, Foldable)

-- | A program without type annotations
type UProgram = Program String ()


freeVarsStmt :: (Ord v) => Stmt v t -> Set v
freeVarsStmt (SIf b s1 s2 _) = freeVarsBExpr b `union` freeVarsStmt s1 `union` freeVarsStmt s2
freeVarsStmt (SYield e _) = freeVarsOExpr e
freeVarsStmt (SOReturn e _) = freeVarsOExpr e
freeVarsStmt (SBReturn b _) = freeVarsBExpr b
freeVarsStmt (SLetOutput (v, _) e s _) = freeVarsOExpr e `union` (freeVarsStmt s `S.difference` singleton v)
freeVarsStmt (SLetBoolean v s _) = freeVarsStmt s `S.difference` singleton v
freeVarsStmt (SSetTrue _ _) = empty
freeVarsStmt (SFor _ (i, v, _) e s _) = freeVarsOExpr e `union` (freeVarsStmt s `S.difference` S.fromList [i, v])
freeVarsStmt (SSeq ss _) = unions (map freeVarsStmt ss)

freeVarsBExpr :: (Ord v) => BExpr v t -> Set v
freeVarsBExpr (BConst _ _) = empty
freeVarsBExpr (BNot b _) = freeVarsBExpr b
freeVarsBExpr (BOp _ b1 b2 _) = freeVarsBExpr b1 `union` freeVarsBExpr b2
freeVarsBExpr (BComp _ e1 e2 _) = freeVarsPExpr e1 `union` freeVarsPExpr e2
freeVarsBExpr (BVar v _) = singleton v
freeVarsBExpr (BGen s _) = freeVarsStmt s
freeVarsBExpr (BApp v es _) = singleton v `union` unions (map (freeVarsOExpr . fst) es)
freeVarsBExpr (BLitEq _ c e _) = freeVarsCExpr c `union` freeVarsOExpr e

freeVarsPExpr :: (Ord v) => PExpr v t -> Set v
freeVarsPExpr (PVar v _) = singleton v

freeVarsCExpr :: (Ord v) => CExpr v t -> Set v
freeVarsCExpr _ = empty

freeVarsOExpr :: (Ord v) => OExpr v t -> Set v
freeVarsOExpr (OVar v _) = singleton v
freeVarsOExpr (OConst _ _) = empty
freeVarsOExpr (OList es _) = unions (map freeVarsOExpr es)
freeVarsOExpr (OApp v es _) = singleton v `union` unions (map (freeVarsOExpr . fst) es)
freeVarsOExpr (OGen s _) = freeVarsStmt s


--- Mapping variable names


mapVarsProgram :: (va -> vb) -> Program va t -> Program vb t
mapVarsProgram f (Program fs m) = Program (map (mapVarsFun f) fs) (f m)

mapVarsFun :: (va -> vb) -> StmtFun va t -> StmtFun vb t
mapVarsFun f (StmtFun v args s t) = StmtFun (f v) newargs (mapVarsStmt f s) t
    where
        newargs = [ (f v, t, map f x) | (v, t, x) <- args ]

mapVarsStmt :: (va -> vb) -> Stmt va t -> Stmt vb t
mapVarsStmt f (SYield o t) = SYield (mapVarsOExpr f o) t
mapVarsStmt f (SOReturn o t) = SOReturn (mapVarsOExpr f o) t
mapVarsStmt f (SBReturn b t) = SBReturn (mapVarsBExpr f b) t
mapVarsStmt f (SIf b s1 s2 t) = SIf (mapVarsBExpr f b) (mapVarsStmt f s1) (mapVarsStmt f s2) t
mapVarsStmt f (SLetOutput (v, t) o s t') = SLetOutput (f v, t) (mapVarsOExpr f o) (mapVarsStmt f s) t'
mapVarsStmt f (SLetBoolean v s t) = SLetBoolean (f v) (mapVarsStmt f s) t
mapVarsStmt f (SSetTrue v t) = SSetTrue (f v) t
mapVarsStmt f (SFor dir (v, t, t'') o s t') = SFor dir (f v, f t, t'') (mapVarsOExpr f o) (mapVarsStmt f s) t'
mapVarsStmt f (SSeq ss t) = SSeq (map (mapVarsStmt f) ss) t
    
mapVarsOExpr :: (va -> vb) -> OExpr va t -> OExpr vb t
mapVarsOExpr f (OVar v t) = OVar (f v) t
mapVarsOExpr f (OConst c t) = OConst (mapVarsCExpr f c) t
mapVarsOExpr f (OList os t) = OList (map (mapVarsOExpr f) os) t
mapVarsOExpr f (OApp v os t) = OApp (f v) (mapVarsArgs f os) t
mapVarsOExpr f (OGen s t) = OGen (mapVarsStmt f s) t
    
mapVarsBExpr :: (va -> vb) -> BExpr va t -> BExpr vb t
mapVarsBExpr f (BConst b t) = BConst b t
mapVarsBExpr f (BNot b t) = BNot (mapVarsBExpr f b) t
mapVarsBExpr f (BOp op b1 b2 t) = BOp op (mapVarsBExpr f b1) (mapVarsBExpr f b2) t
mapVarsBExpr f (BComp comp p1 p2 t) = BComp comp (mapVarsPExpr f p1) (mapVarsPExpr f p2) t
mapVarsBExpr f (BVar v t) = BVar (f v) t
mapVarsBExpr f (BGen s t) = BGen (mapVarsStmt f s) t
mapVarsBExpr f (BApp v os t) = BApp (f v) (mapVarsArgs f os) t
mapVarsBExpr f (BLitEq t c o t') = BLitEq t (mapVarsCExpr f c) (mapVarsOExpr f o) t'

mapVarsPExpr :: (va -> vb) -> PExpr va t -> PExpr vb t
mapVarsPExpr f (PVar v t) = PVar (f v) t

mapVarsCExpr :: (va -> vb) -> CExpr va t -> CExpr vb t
mapVarsCExpr f (CChar c t) = CChar c t
mapVarsCExpr f (CList cs t) = CList (map (mapVarsCExpr f) cs) t

mapVarsArgs :: (va -> vb) -> [(OExpr va t, [PExpr va t])] -> [(OExpr vb t, [PExpr vb t])]
mapVarsArgs f = map (\(o, ps) -> (mapVarsOExpr f o, map (mapVarsPExpr f) ps))


