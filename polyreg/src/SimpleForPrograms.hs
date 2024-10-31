module SimpleForPrograms where

import Control.Monad.State 


data ForTest = Eq | Neq | Lt | Le | Gt | Ge | LabelEq deriving(Eq, Show)

data BinOp = And | Or | Implies deriving(Eq, Show)

-- | Binary operators
-- b = boolean variables
-- p = positions    (ints)
-- l = label values (strings/chars)
data BoolExpr b p l = 
               BoolTrue
             | BoolFalse
             | BoolVar b
             | TestPos ForTest p p
             | LabelAt p l
             | Not (BoolExpr b p l)
             | Bin BinOp (BoolExpr b p l) (BoolExpr b p l)
             deriving(Eq, Show)

data ForDirection = LeftToRight | RightToLeft deriving(Eq,Show)

-- |  For statement
-- p = position variables
-- b = boolean variables
-- alphabet  = label (alphabet alphabet)
-- output = label (output alphabet)
data ForStmt p b alphabet = 
             -- assigns to true
               SetTrue b
             -- if expression
             | If (BoolExpr b p alphabet) [ForStmt p b alphabet] [ForStmt p b alphabet]
             -- for loop with variable a
             -- direction, and using boolean
             -- variables [b].
             | For p ForDirection [b] [ForStmt p b alphabet]
             -- prints what is a position p
             | PrintPos p
             -- prints the value "l" directly
             | PrintLbl alphabet 
             deriving (Eq, Show)

data ForProgram p b alphabet = ForProgram [p] [ForStmt p b alphabet] deriving(Eq, Show)


data ProgramDirection = IfTrue | IfFalse | PositionAt Int deriving(Eq, Show)
data ProgramPosition  = ProgramPosition [ProgramDirection] deriving(Eq, Show)


data InterpreterState b p = InterpreterState {
    booleans  :: b -> Bool,
    positions :: p -> Int 
}

putPosition :: (Eq p) => p -> Int -> State (InterpreterState b p) ()
putPosition p i = do
    s <- get
    put (InterpreterState (booleans s) (\x -> if x == p then i else (positions s x)))

interpretBoolExpr :: (Eq alphabet, Eq b, Eq p) => [alphabet] -> (b -> Bool) -> (p -> Int) -> BoolExpr b p alphabet -> Bool
interpretBoolExpr input b p (BoolVar x) = b x
interpretBoolExpr input b p (BoolTrue) = True
interpretBoolExpr input b p (BoolFalse) = False
interpretBoolExpr input b p (TestPos Eq p1 p2) = p p1 == p p2
interpretBoolExpr input b p (TestPos Neq p1 p2) = p p1 /= p p2
interpretBoolExpr input b p (TestPos Lt p1 p2) = p p1 < p p2
interpretBoolExpr input b p (TestPos Le p1 p2) = p p1 <= p p2
interpretBoolExpr input b p (TestPos Gt p1 p2) = p p1 > p p2
interpretBoolExpr input b p (TestPos Ge p1 p2) = p p1 >= p p2
interpretBoolExpr input b p (TestPos LabelEq p1 p2) = (input !! (p p1)) == (input !! (p p2))
interpretBoolExpr input b p (Not e) = not $ interpretBoolExpr input b p e
interpretBoolExpr input b p (Bin And e1 e2) = interpretBoolExpr input b p e1 && interpretBoolExpr input b p e2
interpretBoolExpr input b p (Bin Or e1 e2) = interpretBoolExpr input b p e1 || interpretBoolExpr input b p e2
interpretBoolExpr input b p (Bin Implies e1 e2) = not (interpretBoolExpr input b p e1) || interpretBoolExpr input b p e2
interpretBoolExpr input b p (LabelAt p1 l) = (input !! (p p1)) == l

interpretStmt :: (Eq alphabet, Eq b, Eq p) =>  [alphabet] -> ForStmt p b alphabet -> State (InterpreterState b p) [alphabet]
interpretStmt input (SetTrue b) = do
  f <- gets booleans
  p <- gets positions
  put (InterpreterState (\x -> if x == b then True else f x) p)
  return []
interpretStmt input (If expr trueBranch falseBranch) = do
  f <- gets booleans
  p <- gets positions
  if interpretBoolExpr input f p expr then
    interpretStmts input trueBranch
  else
    interpretStmts input falseBranch
interpretStmt input (For p direction boolVars stmts) = do
    f <- gets booleans
    oldp <- gets positions
    let positions = case direction of
                        LeftToRight -> [0 .. length input - 1]
                        RightToLeft -> reverse [0 .. length input - 1]
    let new_state = \x -> if x `elem` boolVars then False else f x
    content <- mapM (\x -> putPosition p x >> interpretStmts input stmts) positions
    new_bools <- gets booleans
    -- shadowing variables
    put (InterpreterState (\x -> if x `elem` boolVars then f x else new_bools x) oldp)
    return $ concat content
interpretStmt input (PrintPos p) = do
    positionsTable <- gets positions
    return [input !! (positionsTable p)]
interpretStmt input (PrintLbl l) = return [l]

interpretStmts :: (Eq alphabet, Eq b, Eq p) => [alphabet] -> [ForStmt p b alphabet] -> State (InterpreterState b p) [alphabet]
interpretStmts input stmts = do
    content <- mapM (interpretStmt input) stmts
    return $ concat content


runProgram :: (Eq alphabet, Eq b, Eq p) => ForProgram p b alphabet -> [alphabet] -> [alphabet]
runProgram (ForProgram positions stmts) input = evalState (interpretStmts input stmts) (InterpreterState (\x -> False) (\x -> -1))
