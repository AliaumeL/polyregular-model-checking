{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module ForPrograms where

import           Data.Set (Set, empty, singleton, union, unions)
import qualified Data.Set as S

data BOp = And | Or | Impl | Iff 
    deriving (Show, Eq)

data Comp = Eq | Neq | Lt | Gt | Leq | Geq
    deriving (Show, Eq)

-- | we add a type parameter "t" for decorating the AST with types later on
data BExpr v t = BConst Bool t
               | BNot (BExpr v t) t
               | BOp BOp (BExpr v t) (BExpr v t) t
               | BComp Comp (PExpr v t) (PExpr v t) t
               | BVar v t
               | BGen (Stmt v t) t
               -- tests
               | BApp v [(OExpr v t, [PExpr v t])] t
               | BLitEq t (CExpr v t) (OExpr v t) t
               deriving (Show, Eq, Functor, Foldable, Traversable)

data PExpr v t = PVar v t
               deriving (Show, Eq, Functor, Foldable, Traversable)

data CExpr v t = CChar Char t
               | CList [CExpr v t] t
               deriving (Show, Eq, Functor, Foldable, Traversable)

instance Semigroup (CExpr v t) where
    CList xs _ <> CList ys _ = CList (xs ++ ys) undefined
    _ <> _ = error "Cannot concatenate"

data OExpr v t = OVar v t
               | OConst (CExpr v t) t
               | OList [OExpr v t] t
               | ORev (OExpr v t) t
               | OIndex (OExpr v t) (PExpr v t) t
               | OApp v [(OExpr v t, [PExpr v t])] t
               | OGen (Stmt v t) t -- generator expression
               deriving (Show, Eq, Functor, Foldable, Traversable)

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
              | SFor (v, v, t) (OExpr v t) (Stmt v t) t
              | SSeq [Stmt v t] t
               deriving (Show, Eq, Functor, Foldable, Traversable)


oExprType :: OExpr v t -> t
oExprType (OVar _ t) = t
oExprType (OConst _ t) = t
oExprType (OList _ t) = t
oExprType (ORev _ t) = t
oExprType (OIndex _ _ t) = t
oExprType (OApp _ _ t) = t
oExprType (OGen _ t) = t


letBooleans :: t -> [String] -> Stmt String t -> Stmt String t
letBooleans _ [] _ = error "Empty list of booleans"
letBooleans t [b] block = SLetBoolean b block t
letBooleans t (b : bs) block = SLetBoolean b (letBooleans t bs block) t

letOutputs :: t -> [(String, OExpr String t)] -> Stmt String t -> Stmt String t
letOutputs _ [] _ = error "Empty list of outputs"
letOutputs t [(v, e)] block = SLetOutput (v, oExprType e) e block t
letOutputs t ((v, e) : es) block = SLetOutput (v, oExprType e) e (letOutputs t es block) t

-- | declares a function with a given type and a block of statements
data StmtFun v t = StmtFun v [(v, t, [v])] (Stmt v t) t
    deriving (Show, Eq, Functor, Foldable, Traversable)

funName :: StmtFun v t -> v
funName (StmtFun v _ _ _) = v


-- | A program is a list of functions together with a "main" entrypoint
data Program v t = Program [StmtFun v t] v
    deriving (Show, Eq, Traversable, Functor, Foldable)

-- | A program without type annotations
type UProgram = Program String ()


freeVarsStmt :: (Ord v, Eq v) => Stmt v t -> Set v
freeVarsStmt (SIf b s1 s2 _) = freeVarsBExpr b `union` freeVarsStmt s1 `union` freeVarsStmt s2
freeVarsStmt (SYield e _) = freeVarsOExpr e
freeVarsStmt (SOReturn e _) = freeVarsOExpr e
freeVarsStmt (SBReturn b _) = freeVarsBExpr b
freeVarsStmt (SLetOutput (v, _) e s _) = freeVarsOExpr e `union` (freeVarsStmt s `S.difference` singleton v)
freeVarsStmt (SLetBoolean v s _) = freeVarsStmt s `S.difference` singleton v
freeVarsStmt (SSetTrue _ _) = empty
freeVarsStmt (SFor (i, v, _) e s _) = freeVarsOExpr e `union` (freeVarsStmt s `S.difference` S.fromList [i, v])
freeVarsStmt (SSeq ss _) = unions (map freeVarsStmt ss)

freeVarsBExpr :: (Ord v, Eq v) => BExpr v t -> Set v
freeVarsBExpr (BConst _ _) = empty
freeVarsBExpr (BNot b _) = freeVarsBExpr b
freeVarsBExpr (BOp _ b1 b2 _) = freeVarsBExpr b1 `union` freeVarsBExpr b2
freeVarsBExpr (BComp _ e1 e2 _) = freeVarsPExpr e1 `union` freeVarsPExpr e2
freeVarsBExpr (BVar v _) = singleton v
freeVarsBExpr (BGen s _) = freeVarsStmt s
freeVarsBExpr (BApp v es _) = singleton v `union` unions (map (freeVarsOExpr . fst) es)
freeVarsBExpr (BLitEq _ c e _) = freeVarsCExpr c `union` freeVarsOExpr e

freeVarsPExpr :: (Ord v, Eq v) => PExpr v t -> Set v
freeVarsPExpr (PVar v _) = singleton v

freeVarsCExpr :: (Ord v, Eq v) => CExpr v t -> Set v
freeVarsCExpr _ = empty

freeVarsOExpr :: (Ord v, Eq v) => OExpr v t -> Set v
freeVarsOExpr (OVar v _) = singleton v
freeVarsOExpr (OConst _ _) = empty
freeVarsOExpr (OList es _) = unions (map freeVarsOExpr es)
freeVarsOExpr (ORev e _) = freeVarsOExpr e
freeVarsOExpr (OIndex e p _) = freeVarsOExpr e `union` freeVarsPExpr p
freeVarsOExpr (OApp v es _) = singleton v `union` unions (map (freeVarsOExpr . fst) es)
freeVarsOExpr (OGen s _) = freeVarsStmt s
