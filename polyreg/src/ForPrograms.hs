module ForPrograms where

import Data.Void
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map


-- | v = variable names 
-- | a = atom names (to bind positions to output variables)
data Types v a = Boolean | Position a | Output OutputType | Function (FunctionType v a)
    deriving (Show, Eq)

data OutputType = Unit | OutputOne | OutputList OutputType 
    deriving (Show, Eq)


-- | A function takes as input
--  (w, positions in w)
--  (u, positions in u)
--  etc...
--  So its input type is a list of pairs of output types and the number of positions in that output type
data FunctionType v a = 
        FunctionOutput   [(OutputType, Int)] OutputType
      | FunctionBoolean  [(OutputType, Int)]
    deriving (Show, Eq)

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
               | BLitEq (CExpr v t) (OExpr v t) t
               deriving (Show, Eq)

data PExpr v t = PVar v t
               deriving (Show, Eq)

data CExpr v t = CChar Char t
               | CUnit t
               | CList [CExpr v t] t
               deriving (Show, Eq)

instance Semigroup (CExpr v t) where
    CList xs _ <> CList ys _ = CList (xs ++ ys) undefined
    CUnit _ <> x = x
    x <> CUnit _ = x
    _ <> _ = error "Cannot concatenate"

instance Monoid t => Monoid (CExpr v t) where
    mempty = CUnit mempty

data OExpr v t = OVar v t
               | OConst (CExpr v t) t
               | OList [OExpr v t] t
               | ORev (OExpr v t) t
               | OIndex (OExpr v t) (PExpr v t) t
               | OApp v [(OExpr v t, [PExpr v t])] t
               | OGen (Stmt v t) t -- generator expression
               deriving (Show, Eq)

-- For statements:
-- 1. Function declarations
-- 2. Block of statements
-- 3. A single statement
data Stmt v t = SIf (BExpr v t) (Stmt v t) (Stmt v t) t
              | SYield (OExpr v t) t
              | SOReturn (OExpr v t) t
              | SBReturn (BExpr v t) t
              | SLetOutput v (OExpr v t) (Stmt v t) t
              | SLetBoolean v (Stmt v t) t
              | SSetTrue v t
              | SFor (v, v) (OExpr v t) (Stmt v t) t
              | SSeq [Stmt v t] t
               deriving (Show, Eq)

letBooleans :: [String] -> Stmt String () -> Stmt String ()
letBooleans [] _ = error "Empty list of booleans"
letBooleans [b] block = SLetBoolean b block ()
letBooleans (b : bs) block = SLetBoolean b (letBooleans bs block) ()

letOutputs :: [(String, OExpr String ())] -> Stmt String () -> Stmt String ()
letOutputs [] _ = error "Empty list of outputs"
letOutputs [(v, e)] block = SLetOutput v e block ()
letOutputs ((v, e) : es) block = SLetOutput v e (letOutputs es block) ()

-- | declares a function with a given type and a block of statements
data StmtFun v t = StmtFun v [(v, [v])] (Stmt v t) t
    deriving (Show, Eq)

funName :: StmtFun v t -> v
funName (StmtFun v _ _ _) = v


-- | A program is a list of functions together with a "main" entrypoint
data Program v t = Program [StmtFun v t] v t
    deriving (Show, Eq)

-- | A program without type annotations
type UProgram = Program String ()

-- | A program with type annotations
type TProgram = Program String (Types String Int)


