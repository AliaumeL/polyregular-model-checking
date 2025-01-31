{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.Simple where

import Logic.QuantifierFree

import Control.Monad
import Control.Monad.State 
import Control.Monad.Except

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.List

newtype PName = PName String deriving(Eq, Show,Ord)
newtype BName = BName String deriving(Eq, Show,Ord)

-- | Binary operators
-- b = boolean variables
-- p = positions    (ints)
-- l = label values (strings/chars)
data BoolExpr = 
                BConst   Bool
              | BVar     BName
              | BTest    TestOp PName PName
              | BLabelAt PName Char
              | BNot     BoolExpr
              | BBin     BinOp BoolExpr BoolExpr
              deriving(Eq, Show)

data Direction = LeftToRight | RightToLeft deriving(Eq,Show)

-- |  For statement
-- p = position variables
-- b = boolean variables
-- alphabet  = label (alphabet alphabet)
-- output = label (output alphabet)
data ForStmt  = 
             -- assigns to true
               SetTrue BName
             -- if expression
             | If BoolExpr ForStmt ForStmt
             -- for loop with variable a
             -- direction, and using boolean
             -- variables [b].
             | For PName Direction [BName] ForStmt
             -- prints what is a position p
             | PrintPos PName
             -- prints the value "l" directly
             | PrintLbl Char
             -- sequence of statements
             | Seq [ForStmt]
             deriving (Eq, Show)

data ForProgram = ForProgram [BName] ForStmt deriving(Eq, Show)


programDepth :: ForProgram -> Int
programDepth (ForProgram _ stmt) = programDepth' stmt
    where
        programDepth' (SetTrue _) = 1
        programDepth' (If _ t f) = max (programDepth' t) (programDepth' f)
        programDepth' (For _ _ _ stmt) = 1 + programDepth' stmt
        programDepth' (PrintPos _) = 1
        programDepth' (PrintLbl _) = 1
        programDepth' (Seq []) = 1
        programDepth' (Seq stmts) = maximum $ map programDepth' stmts

programSize :: ForProgram -> Int
programSize (ForProgram _ stmt) = programSize' stmt
    where
        programSize' (SetTrue _) = 1
        programSize' (If e t f) = 1 + programSize' t + programSize' f
        programSize' (For _ _ _ stmt) = 1 + programSize' stmt
        programSize' (PrintPos _) = 1
        programSize' (PrintLbl _) = 1
        programSize' (Seq stmts) = sum $ map programSize' stmts

programBoolDepth :: ForProgram -> Int
programBoolDepth (ForProgram _ stmt) = programBoolDepth' stmt
    where
        programBoolDepth' (SetTrue _) = 0
        programBoolDepth' (If e t f) = max (programBoolDepth' t) (programBoolDepth' f)
        programBoolDepth' (For _ _ l stmt) = length l + programBoolDepth' stmt
        programBoolDepth' (PrintPos _) = 0
        programBoolDepth' (PrintLbl _) = 0
        programBoolDepth' (Seq [])    = 0
        programBoolDepth' (Seq stmts) = maximum $ map programBoolDepth' stmts

programYieldCount :: ForProgram -> Int
programYieldCount (ForProgram _ _) = undefined


data Movement = MoveIfL  BoolExpr
              | MoveIfR  BoolExpr
              | MoveSeq  Int
              | MoveFor  PName Direction [BName]
              | MoveProg [BName]
              deriving(Eq, Show)

data Path = Path [Movement] deriving (Eq, Show)


pathBVars :: Path -> [BName]
pathBVars (Path []) = []
pathBVars (Path (MoveIfL e : ms)) = pathBVars (Path ms)
pathBVars (Path (MoveIfR e : ms)) = pathBVars (Path ms)
pathBVars (Path (MoveSeq _ : ms)) = pathBVars (Path ms)
pathBVars (Path (MoveFor _ _ bs : ms)) = bs ++ pathBVars (Path ms)
pathBVars (Path (MoveProg bs : ms)) = bs ++ pathBVars (Path ms)

pathPVars :: Path -> [PName]
pathPVars (Path []) = []
pathPVars (Path (MoveIfL e : ms)) = pathPVars (Path ms)
pathPVars (Path (MoveIfR e : ms)) = pathPVars (Path ms)
pathPVars (Path (MoveSeq _ : ms)) = pathPVars (Path ms)
pathPVars (Path (MoveFor p _ _ : ms)) = p : pathPVars (Path ms)
pathPVars (Path (MoveProg _ : ms)) = pathPVars (Path ms)

pathToTag :: Path -> String
pathToTag (Path ms) = concat . intersperse "_" . map movementToTag $ ms
    where
        movementToTag (MoveIfL e) = "l"
        movementToTag (MoveIfR e) = "r"
        movementToTag (MoveSeq n) = show n  
        movementToTag (MoveFor p d bs) = "f"
        movementToTag (MoveProg bs) = "s"

tagToPath :: String -> Path
tagToPath s = Path $ map tagToMovement s -- FIXME: split on underscores first!
    where
        tagToMovement 'l' = MoveIfL (BConst True)
        tagToMovement 'r' = MoveIfR (BConst True)
        tagToMovement 'f' = MoveFor (PName "p") LeftToRight []
        tagToMovement 's' = MoveProg []
        tagToMovement c = MoveSeq (read [c])

followPath :: Path -> ForStmt -> ForStmt
followPath (Path []) stmt = stmt
followPath (Path (MoveIfL e : ms)) (If e' t f) = followPath (Path ms) t
followPath (Path (MoveIfR e : ms)) (If e' t f) = followPath (Path ms) f
followPath (Path (MoveSeq n : ms)) (Seq stmts) = followPath (Path ms) (stmts !! n)
followPath (Path (MoveFor p d bs : ms)) (For p' d' bs' stmt) = followPath (Path ms) stmt

followPathProg :: Path -> ForProgram -> ForStmt
followPathProg (Path (_ : p)) (ForProgram bs stmt) = followPath (Path p) stmt
followPathProg (Path []) (ForProgram bs stmt) = stmt


listPrintStatements :: ForProgram -> [Path]
listPrintStatements prog = do 
    pos <- listPositions prog
    let stmt = followPathProg pos prog
    case stmt of
        PrintPos _ -> return pos
        PrintLbl _ -> return pos
        _ -> []

-- TODO: remove duplicates 
listAlphabet :: ForProgram -> String
listAlphabet (ForProgram _ stmt) = S.toList $ listAlphabet' stmt
    where
        listAlphabet' :: ForStmt -> Set Char
        listAlphabet' (SetTrue _) = S.empty
        listAlphabet' (If e t f) = listAlphabetBExpr e `S.union` listAlphabet' t `S.union` listAlphabet' f
        listAlphabet' (For _ _ _ stmt) = listAlphabet' stmt
        listAlphabet' (PrintPos _) = S.empty
        listAlphabet' (PrintLbl l) = S.singleton l
        listAlphabet' (Seq stmts) = S.unions $ map listAlphabet' stmts

        listAlphabetBExpr :: BoolExpr -> Set Char
        listAlphabetBExpr (BConst _) = S.empty
        listAlphabetBExpr (BVar _) = S.empty
        listAlphabetBExpr (BTest _ _ _) = S.empty
        listAlphabetBExpr (BLabelAt _ l) = S.singleton l
        listAlphabetBExpr (BNot e) = listAlphabetBExpr e
        listAlphabetBExpr (BBin _ e1 e2) = listAlphabetBExpr e1 `S.union` listAlphabetBExpr e2




listMovements :: ForProgram -> [[Movement]]
listMovements (ForProgram bs stmt) = map (\p -> (MoveProg bs) : p) . movements' $ stmt
    where
        movements' :: ForStmt -> [[Movement]]
        movements' (SetTrue b) = [[]]
        movements' (If e t f) = map (MoveIfL e :) (movements' t) ++ map (MoveIfR e :) (movements' f)
        movements' (For p d bs stmt) = map (MoveFor p d bs :) (movements' stmt)
        movements' (PrintPos _) = [[]]
        movements' (PrintLbl _) = [[]]
        movements' (Seq stmts) = do
            (i, stmt) <- zip [0..] stmts
            ms <- movements' stmt
            return $ MoveSeq i : ms

listPositions :: ForProgram -> [Path]
listPositions p = map Path $ listMovements p




class (Monad m) => MonadInterpreter m where
    throwWithCtx :: String -> m a

    setTrue      :: BName -> m ()
    withBools    :: [BName] -> m a -> m a
    withLoopPos  :: PName -> Direction -> m a -> m [a]

    getPos       :: PName -> m Int
    getBool      :: BName -> m Bool
    getCharAt    :: PName -> m Char


data InterpreterState = InterpreterState {
    input     :: String,
    booleans  :: Map BName Bool,
    posChars  :: Map PName Char,
    positions :: Map PName Int
} deriving (Eq,Show)

data InterpreterError = InterpreterError String InterpreterState  deriving (Eq,Show)

newtype InterM a = InterM (StateT InterpreterState (Except InterpreterError) a)
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError InterpreterError) 

runInterM :: InterM a -> InterpreterState -> Either InterpreterError a 
runInterM (InterM m) s = runExcept $ evalStateT m s

listOldValues :: [BName] -> Map BName Bool -> [(BName, Bool)]
listOldValues [] _ = []
listOldValues (x : xs) m = case M.lookup x m of
    Just b -> (x, b) : listOldValues xs m
    Nothing -> listOldValues xs m

iterWord :: Direction -> String -> [(Int, Char)]
iterWord LeftToRight s = zip [0..] s
iterWord RightToLeft s = reverse (zip [0..] s)

instance MonadInterpreter InterM where
    throwWithCtx msg = do
        s <- get
        throwError $ InterpreterError msg s

    setTrue b = do
        s <- get
        put $ s { booleans = M.insert b True (booleans s) }

    withBools bs m = do
        s <- get
        let oldValues = M.fromList $ listOldValues bs (booleans s)
        put $ s { booleans = (M.fromList $ zip bs (repeat False)) `M.union` (booleans s) }
        r <- m
        modify (\s -> s { booleans = M.union oldValues (booleans s)})
        return r

    withLoopPos p d m = do
        input <- gets input
        forM (iterWord d input) $ \(i, c) -> do
            s <- get
            put $ s { positions = M.insert p i (positions s), posChars = M.insert p c (posChars s)}
            r <- m
            modify (\s -> s { positions = M.delete p (positions s), posChars = M.delete p (posChars s)})
            return r

    getPos p = do
        s <- get
        case M.lookup p (positions s) of
            Just i -> return i
            Nothing -> throwWithCtx $ "Position " ++ show p ++ " not found"

    getBool b = do
        s <- get
        case M.lookup b (booleans s) of
            Just b -> return b
            Nothing -> throwWithCtx $ "Boolean " ++ show b ++ " not found"

    getCharAt p = do
        s <- get
        case M.lookup p (posChars s) of
            Just c -> return c
            Nothing -> throwWithCtx $ "Position " ++ show p ++ " not found"


interpretPosExprM :: (MonadInterpreter m) => PName -> m Int
interpretPosExprM p = getPos p

interpretBoolExprM :: (MonadInterpreter m) => BoolExpr -> m Bool
interpretBoolExprM (BConst b) = return b
interpretBoolExprM (BVar b) = getBool b
interpretBoolExprM (BTest op e1 e2) = (testOpSemantics op) <$> interpretPosExprM e1 <*> interpretPosExprM e2
interpretBoolExprM (BLabelAt p l) = (== l) <$> getCharAt p
interpretBoolExprM (BNot e) = not <$> interpretBoolExprM e
interpretBoolExprM (BBin op e1 e2) = (binOpSemantics op) <$> interpretBoolExprM e1 <*> interpretBoolExprM e2


interpretStmtM :: (MonadInterpreter m) => ForStmt -> m String
interpretStmtM (SetTrue b) = setTrue b >> return ""
interpretStmtM (If e t f) = do
    b <- interpretBoolExprM e
    if b then interpretStmtM t else interpretStmtM f
interpretStmtM (For p d bs stmt) = do
    strings <- withLoopPos p d (withBools bs (interpretStmtM stmt))
    return . concat $ strings
interpretStmtM (PrintPos p) = pure <$> getCharAt p
interpretStmtM (PrintLbl l) = return [l]
interpretStmtM (Seq stmts) = concat <$> mapM interpretStmtM stmts

interpretProgramM :: (MonadInterpreter m) => ForProgram -> m String
interpretProgramM (ForProgram bs stmt) = withBools bs $ interpretStmtM stmt

interpretProgram :: ForProgram -> InterpreterState -> Either InterpreterError String
interpretProgram p s = runInterM (interpretProgramM p) s


runProgram :: ForProgram -> String -> Either InterpreterError String
runProgram  p s = interpretProgram p (InterpreterState s M.empty M.empty M.empty)



prettyPrintForProgram :: ForProgram -> String
prettyPrintForProgram (ForProgram bs stmt) = prettyPrintBoolList 0 bs ++ prettyPrintForStmt 0 stmt

indentStr :: Int -> String -> String
indentStr n s = replicate n ' ' ++ s

-- prints comma separated list of boolean variables
-- with indentation level n
-- knowing that lines cannot be longer than 80 characters (so we split them)
prettyPrintBoolList :: Int -> [BName] -> String
prettyPrintBoolList _ [] = ""
prettyPrintBoolList n bs = line ++ "\n"
  where 
    names = (map (\(BName b) -> b) bs) :: [String]
    line = "let " ++ (concat $ intersperse ", " names) ++ " := false in"
    -- (ans, _) = foldl' f ("", length indent) bs
    -- indent = replicate n ' '
    -- initLen = length indent
    -- f :: (String, Int) -> BName -> (String, Int)
    -- f (ans, size) (BName b) = 
    --     let bsize = length b in
    --     let size' = size + bsize + 2 in
    --     if size' > 80 then (ans ++ "\n" ++ indent ++ b ++ ", ", initLen + bsize + 2) else (ans ++ b ++ ", ", size')

prettyPrintForStmt :: Int -> ForStmt -> String
prettyPrintForStmt n (SetTrue (BName b)) = indentStr n $ b ++ " := true" ++ "\n"
prettyPrintForStmt n (If e t f) = 
    let indent = replicate n ' ' in
    let e' = prettyPrintBoolExpr e in
    let t' = prettyPrintForStmt (n + 1) t in
    let f' = prettyPrintForStmt (n + 1) f in
    indent ++ "if " ++ e' ++ " then\n" ++ t' ++ indent ++ "else\n" ++ f' ++ indent ++ "endif\n"
prettyPrintForStmt n (If e t (Seq [])) = 
    let indent = replicate n ' ' in
    let e' = prettyPrintBoolExpr e in
    let t' = prettyPrintForStmt (n + 1) t in
    indent ++ "if " ++ e' ++ " then\n" ++ t' ++ indent ++ "endif\n"
prettyPrintForStmt n (For (PName p) d bs stmt) =
    let indent = replicate n ' ' in
    let d' = case d of
            LeftToRight -> "input"
            RightToLeft -> "reversed(input)" in
    let bs'   = prettyPrintBoolList (n + 1) bs in
    let stmt' = prettyPrintForStmt (n + 1) stmt in
    indent ++ "for " ++ p ++ " in " ++ d' ++ " do\n" ++ bs' ++ stmt' ++ indent ++ "done\n"
prettyPrintForStmt n (PrintPos (PName p)) = indentStr n $ "print " ++ p ++ "\n"
prettyPrintForStmt n (PrintLbl l) = indentStr n $ "print " ++ show l ++ "\n"
prettyPrintForStmt n (Seq []) = indentStr n $ "skip\n"
prettyPrintForStmt n (Seq stmts) = concatMap (prettyPrintForStmt n) stmts
prettyPrintForStmt _ _ = error "prettyPrintForStmt: not implemented"

prettyPrintBoolExpr :: BoolExpr -> String 
prettyPrintBoolExpr (BConst b) = show b
prettyPrintBoolExpr (BVar (BName b)) = b
prettyPrintBoolExpr (BTest op (PName p1) (PName p2)) = p1 ++ " " ++ show op ++ " " ++ p2
prettyPrintBoolExpr (BLabelAt (PName p) l) = "label(" ++ p ++ ") == " ++ show l
prettyPrintBoolExpr (BNot e) = "not " ++ prettyPrintBoolExpr e
prettyPrintBoolExpr (BBin op e1 e2) = "(" ++ prettyPrintBoolExpr e1 ++ ")" ++ " " ++ show op ++ " " ++ "(" ++ prettyPrintBoolExpr e2 ++ ")"



skipLastLetterProgEx :: ForProgram
skipLastLetterProgEx = ForProgram [] (
        For (PName "i") LeftToRight [BName "b"] (
            For (PName "j") RightToLeft [] (
                If (BVar (BName "b")) (
                    If (BTest Eq (PName "j") (PName "i")) 
                       (PrintPos (PName "j"))
                       (Seq [])
                ) (
                    (SetTrue (BName "b"))
                )
            )
        )
    )
