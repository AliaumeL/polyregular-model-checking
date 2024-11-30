module FOTranslation where

import Control.Monad.State

--
-- This module performs the translation 
-- from a Simple For Program (SFP) into
-- a First Order Interpretation (FOI).
--
-- We provide a De Brujin index version of the 
-- for statements. This simplifies writing formulas.
-- We also provide an intermediate representation of 
-- formulas using De Brujin indices.
--
-- Also, we keep track of input/output
-- variables and distinguish them from quantified
-- ones, in order to simplify writing our compositional
-- transition monoid.
--
-- This module is completely independent, and we 
-- convert from the usual For statements into the De Brujin indexes,
-- and back to FO interpretations using usual variable names.

import QuantifierFree

newtype BoolDB = BoolDB Int deriving (Show, Eq)
newtype PosDB  = PosDB  Int deriving (Show, Eq)

data BoolExprDB = BConst   Bool 
                | BBin     BinOp BoolExprDB BoolExprDB
                | BNot     BoolExprDB
                | BPosPred TestOp PosDB PosDB
                | BCharAt  PosDB Char
                | BVar     BoolDB
                  deriving(Eq,Show)

data Direction = LTR | RTL deriving(Eq,Show)

data ForStmtDB = SetTrue Int
               | If BoolExprDB ForStmtDB ForStmtDB
               -- for introduces
               -- 1. new position variable
               -- 2. "n" new boolean variables
               | For Int Direction ForStmtDB
               -- print the value at position i
               | PrintPos  PosDB
               -- print a character
               | PrintChar Char
               -- Sequence
               | Seq [ForStmtDB]
               deriving (Show, Eq)


-- How to navigate in a source tree of ForStmtDB
data Movement = MovIfLeft  BoolExprDB
              | MovIfRight BoolExprDB
              | MovFor     Int Direction
              | MovSeq     Int
              deriving (Show, Eq)

newtype SourcePath = SourcePath [Movement] deriving (Show, Eq)


andThenMove :: Movement -> SourcePath -> SourcePath
andThenMove m (SourcePath ms) = SourcePath (m:ms)


booleanVariables :: SourcePath -> Int
booleanVariables (SourcePath []) = 0
booleanVariables (SourcePath (MovIfLeft _ : ms)) = booleanVariables (SourcePath ms)
booleanVariables (SourcePath (MovIfRight _ : ms)) = booleanVariables (SourcePath ms)
booleanVariables (SourcePath (MovFor n _ : ms)) = n + booleanVariables (SourcePath ms)
booleanVariables (SourcePath (MovSeq _ : ms)) = booleanVariables (SourcePath ms)

positionVariables :: SourcePath -> Int
positionVariables (SourcePath []) = 0
positionVariables (SourcePath (MovIfLeft _ : ms)) = positionVariables (SourcePath ms)
positionVariables (SourcePath (MovIfRight _ : ms)) = positionVariables (SourcePath ms)
positionVariables (SourcePath (MovFor _ _ : ms)) = 1 + positionVariables (SourcePath ms)
positionVariables (SourcePath (MovSeq _ : ms)) = positionVariables (SourcePath ms)


data Sort = Pos | Bool deriving (Show, Eq)
data Quant = Exists | Forall deriving (Show, Eq)

data FormulaDB = FConst   Bool
               | FVarIn   BoolDB -- input  boolean variable
               | FVarOut  BoolDB -- output boolean variable
               | FVar     BoolDB -- boolean variable (internally quantified)
               | FBin     BinOp FormulaDB FormulaDB
               | FNot     FormulaDB
               | FPosPred TestOp PosDB PosDB
               | FCharAt  PosDB Char
               | FQuant   Quant Sort FormulaDB
               deriving (Show, Eq)



injectBoolExpr :: (BoolDB -> FormulaDB) -> BoolExprDB -> FormulaDB
injectBoolExpr f (BConst b) = FConst b
injectBoolExpr f (BBin op l r) = FBin op (injectBoolExpr f l) (injectBoolExpr f r)
injectBoolExpr f (BNot x) = FNot (injectBoolExpr f x)
injectBoolExpr f (BPosPred op p1 p2) = FPosPred op p1 p2
injectBoolExpr f (BCharAt p c) = FCharAt p c
injectBoolExpr f (BVar b) = f b


andList :: [FormulaDB] -> FormulaDB
andList [] = FConst True
andList [x] = x
andList (x:xs) = FBin Conj x (andList xs)

orList :: [FormulaDB] -> FormulaDB
orList [] = FConst False
orList [x] = x
orList (x:xs) = FBin Disj x (orList xs)


-- replaces every input/output variable by a corresponding formula
remapInputOutput :: [FormulaDB] -> [FormulaDB] -> FormulaDB -> FormulaDB
remapInputOutput input output (FVarIn (BoolDB b)) = input !! b
remapInputOutput input output (FVarOut (BoolDB b)) = output !! b
remapInputOutput input output (FVar b) = FVar b
remapInputOutput input output (FConst b) = FConst b
remapInputOutput input output (FBin op l r) = FBin op (remapInputOutput input output l) (remapInputOutput input output r)
remapInputOutput input output (FNot f) = FNot (remapInputOutput input output f)
remapInputOutput input output (FPosPred op p1 p2) = FPosPred op p1 p2
remapInputOutput input output (FCharAt p c) = FCharAt p c


-- Transition creates a formula
-- that represents the transition in Boolean variables
-- operated by a block of code.
-- 
-- The FormulaDB uses De Brujin indices to represent
-- variables and positions.
--
-- The SourcePath is a path in the source tree that
-- leads to the current code block.
--
-- The ForStmtDB is the current code block.
--
-- [ setTrue b ] = all boolean variables are unchanged except b which is set to true.
transition :: SourcePath -> ForStmtDB -> FormulaDB
transition sp (SetTrue b) = FBin Conj (FVarOut . BoolDB $ b) f
    where 
        bs = filter (/= b) $ [1..booleanVariables sp]
        bsIn = map (FVarIn . BoolDB) bs
        bsOut = map (FVarOut . BoolDB) bs
        f = andList $ map (\(x,y) -> FBin Equiv x y) $ zip bsIn bsOut
-- [ if e l r ] = exists b. b <=> e /\ b => [l] ∧ ¬b => [r]
transition sp (If e l r) = f
    where
        bsize = booleanVariables sp
        bs = [1..bsize]
        -- a fresh varible.
        bp = FVar (BoolDB 1)
        bIn = map (FVarIn . BoolDB)  bs
        bOut = map (FVarOut . BoolDB)  bs
        φ = transition (MovIfLeft e `andThenMove` sp) l
        ψ = transition (MovIfRight e `andThenMove` sp) r
        f = FQuant Exists Bool (andList [bpPos, bpNeg, bpDef])
        bpPos = FBin Impl bp φ
        bpNeg = FBin Impl (FNot $ bp) ψ
        bpDef = FBin Equiv bp (injectBoolExpr FVarIn e)
-- [ for i d body ] = 
-- exists positions i1,...,in. 
-- exists boolean variables (bd)_1, ..., (bd)_n.
-- 1. i1 <= i2 <= ... <= in
-- 2. [body]((bd)_k, j i_k, (bd)_(k+1))
-- 3. (bd)_0 = b (false, ..., false)
-- 4. [body]( (bd)_k, j i, (bd)_k) for all i_k < i < i_{k+1}
--     (i.e., no other modifications of boolean variable happens)
-- 5. [body]( (bd)_n, j i , b) for all i_n < i
transition sp (For i d body) = undefined
-- [ printPos i ] = everything stays exactly the same
transition sp (PrintPos i) = f
    where
        bs = map BoolDB [1..booleanVariables sp]
        bsIn = map FVarIn bs
        bsOut = map FVarOut bs
        f = andList $ map (\(x,y) -> FBin Equiv x y) $ zip bsIn bsOut
-- [ printChar c ] = everything stays exactly the same
transition sp (PrintChar c) = f
    where
        bs = map BoolDB [1..booleanVariables sp]
        bsIn = map FVarIn bs
        bsOut = map FVarOut bs
        f = andList $ map (\(x,y) -> FBin Equiv x y) $ zip bsIn bsOut
-- [ seq [s1, s2, ..., sn] ] = exists b12, b23, ..., b(n-1)n. [s1](b1,b2) /\ [s2](b2,b3) /\ ... /\ [sn](b(n-1),bn)
transition sp (Seq ss) = undefined


-- Now, we need, given a source path, a whole program,
-- and a boolean expression "b", to construct a formula
-- deciding if "b" holds (taking as arguments the input position variables only)
--
-- To that end, we need to go to this precise source path, and
-- *unroll* loops enough to reach the boolean expression.
--
-- [(For <- body), enterFor ] = compute "body" up to the "i-1" time and then enter the loop
--
-- [Seq cs, SeqNumber i] = compute the transition function of the prefix of length "i"
--
-- [If e l r, IfLeft] = compute the transition function of the "l" branch (does not care about e)
-- [If e l r, IfRight] = compute the transition function of the "r" branch (does not care about e)
--
isSatisfied :: SourcePath -> ForStmtDB -> BoolExprDB -> FormulaDB
isSatisfied = undefined

-- Finally, we can leverage this to produce
-- a selection function. It collects all the boolean tests
-- above a given source path and takes the conjunct of 
-- the corresponding "isSatisfied" formulas.
shouldBeProduced :: ForStmtDB -> SourcePath -> FormulaDB
shouldBeProduced p sp = andList $ map (\(sp, b) -> isSatisfied sp p b) $ booleanTestsAbove sp
    where
        booleanTests :: [Movement] -> [(SourcePath, BoolExprDB)]
        booleanTests [] = []
        booleanTests m@(MovIfLeft  b : ms) = (SourcePath m, b) : booleanTests ms
        booleanTests m@(MovIfRight b : ms) = (SourcePath m, b) : booleanTests ms
        booleanTests m@(MovFor _ _ : ms) = booleanTests ms
        booleanTests m@(MovSeq _ : ms) = booleanTests ms

        booleanTestsAbove :: SourcePath -> [(SourcePath, BoolExprDB)]
        booleanTestsAbove (SourcePath m) = map (\(SourcePath m, b) -> (SourcePath (reverse m), b)) . booleanTests . reverse $ m

-- Let us now compute Order formula
compareSourcePaths :: SourcePath -> SourcePath -> FormulaDB
compareSourcePaths (SourcePath m1) (SourcePath m2) = undefined

-- And the Label formula
shouldProduceChar :: SourcePath -> Char -> FormulaDB
shouldProduceChar sp c = undefined

-- And the Copy formula
shouldCopyChar :: SourcePath -> Int -> FormulaDB
shouldCopyChar sp i = undefined


data FoInterpretationDB = FoInterpretationDB {
    domainFormula  :: SourcePath -> FormulaDB,
    orderFormula   :: SourcePath -> SourcePath -> FormulaDB,
    labelFormula   :: SourcePath -> Char -> FormulaDB,
    copyFormula    :: SourcePath -> Int -> FormulaDB,
    arity          :: SourcePath -> Int,
    maxArity       :: Int
}

-- We can now conclude the translation

toFoInterpretation :: ForStmtDB -> FoInterpretationDB
toFoInterpretation p = FoInterpretationDB {
    domainFormula = shouldBeProduced p,
    orderFormula  = compareSourcePaths,
    labelFormula  = shouldProduceChar,
    copyFormula   = shouldCopyChar,
    arity         = undefined,
    maxArity      = undefined
}



--- Evaluations 

data EvalFormulaState = EvalFormulaState {
    inputBoolValues :: BoolDB -> Bool,
    outputBoolValues :: BoolDB -> Bool,
    booleanValues :: BoolDB -> Bool,
    positionValues :: PosDB -> Int
}

evalFormulaDB :: EvalFormulaState -> String -> FormulaDB -> Bool
evalFormulaDB s w (FConst b) = b
evalFormulaDB s w (FVarIn b) = inputBoolValues s b
evalFormulaDB s w (FVarOut b) = outputBoolValues s b
evalFormulaDB s w (FVar b) = booleanValues s b
evalFormulaDB s w (FBin op l r) = evalBin op (evalFormulaDB s w l) (evalFormulaDB s w r)
evalFormulaDB s w (FNot f) = not (evalFormulaDB s f)
evalFormulaDB s w (FPosPred op p1 p2) = evalTest op (positionValues s p1) (positionValues s p2)
evalFormulaDB s w (FCharAt p c) = (w !! positionValues s p) == c
evalFormulaDB s w (FQuant Exists Pos f) = any (\i -> evalFormulaDB (s { positionValues = \(PosDB p) -> if p == 1 then i else positionValues s (PosDB (p-1)) }) w f) [0..length w]
evalFormulaDB s w (FQuant Forall Pos f) = all (\i -> evalFormulaDB (s { positionValues = \(PosDB p) -> if p == 1 then i else positionValues s (PosDB (p-1)) }) w f) [0..length w]
evalFormulaDB s w (FQuant Exists Bool f) = any (\i -> evalFormulaDB (s { booleanValues = \(BoolDB b) -> if b == 1 then i else booleanValues s (BoolDB (b-1)) }) w f) [True, False]
evalFormulaDB s w (FQuant Forall Bool f) = all (\i -> evalFormulaDB (s { booleanValues = \(BoolDB b) -> if b == 1 then i else booleanValues s (BoolDB (b-1)) }) w f) [True, False]


data EvalStmtState = EvalStmtState {
    word     :: String,
    boolVars :: BoolDB -> Bool,
    posVars  :: PosDB -> Int
} 

evalStmtDB :: ForStmtDB -> State EvalStmtState String
evalStmtDB (SetTrue b) = do
    s <- get
    put (s { boolVars = \(BoolDB b') -> if b == b' then True else boolVars s (BoolDB b') })
    return True
evalStmtDB (If e l r) = do
    s <- get
    let b = evalFormulaDB (EvalFormulaState (boolVars s) (boolVars s) (boolVars s) (posVars s)) (word s) e
    if b then evalStmtDB l else evalStmtDB r
evalStmtDB (For i d body) = do
    s <- get
    let positions = case d of
                        LTR -> [0 .. length (word s) - 1]
                        RTL -> reverse [0 .. length (word s) - 1]
    let new_state = \x -> if x == i then True else boolVars s (BoolDB x)
    content <- mapM (\x -> put (s { posVars = \(PosDB p) -> if p == 1 then x else posVars s (PosDB (p-1)) }) >> evalStmtDB body) positions
    put (s { boolVars = new_state })
    return $ and content
evalStmtDB (PrintPos p) = do
    s <- get
    return [word s !! posVars s p]
evalStmtDB (PrintChar c) = return [c]
evalStmtDB (Seq ss) = do
    s <- get
    content <- mapM (\x -> put (s { boolVars = \(BoolDB b) -> if b == x then True else boolVars s (BoolDB b) }) >> evalStmtDB x) ss
    return $ concat content

