module ForPrograms where

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Void
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map


-- | v = variable names 
-- | a = atom names (to bind positions to output variables)
data Types v a = Boolean | Position a | Output OutputType | Function (FunctionType v a)
    deriving (Show, Eq)

data OutputType = OutputOne | OutputList OutputType
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


-- We have four type of expressions
-- 1. Boolean expressions
-- 2. Position expressions
-- 3. Constant expressions
-- 4. Output expressions

data BOp = And | Or | Impl | Iff 
    deriving (Show, Eq)

data Comp = Eq | Neq | Lt | Gt | Leq | Geq
    deriving (Show, Eq)

-- | we add a type parameter "t" for decorating the AST with types later on
data BExpr v t = BConst Bool t
               | BNot (BExpr v t) t
               | BOp BOp (BExpr v t) (BExpr v t) t
               | BComp Comp (PExpr v t) (PExpr v t) t
               | BApp v [(OExpr v t, [PExpr v t])] t
               | BLitAt (CExpr v t) (PExpr v t) t
               | BVar v t
               deriving (Show, Eq)

data PExpr v t = PVar v t
               deriving (Show, Eq)

data CExpr v t = CChar Char t
               | CList [CExpr v t] t
               deriving (Show, Eq)

data OExpr v t = OVar v t
               | OList [OExpr v t] t
               | ORev (OExpr v t) t
               | OIndex (OExpr v t) (PExpr v t) t
               | OApp v [(OExpr v t, [PExpr v t])] t
               | OGen (StmtBlock v t) t -- generator expression
               deriving (Show, Eq)

-- 
-- For statements
-- 1. Function declarations
-- 2. Block of statements
-- 3. A single statement
data Stmt v t = SIf (BExpr v t) (StmtBlock v t) (StmtBlock v t) t
              | SYield (OExpr v t) t
              | SReturn (OExpr v t) t
              | SLetOutput v (OExpr v t) (StmtBlock v t) t
              | SLetBoolean [v] (StmtBlock v t) t
              | SSetTrue v t
              | SFor (v, v) v (StmtBlock v t) t
               deriving (Show, Eq)

-- | declares some variables to be False, and executes a block of statements
data StmtBlock v t = StmtBlock [Stmt v t] t
    deriving (Show, Eq)

-- | declares a function with a given type and a block of statements
data StmtFun v t = StmtFun v [(v, [v])] (StmtBlock v t) t
    deriving (Show, Eq)


-- | A program is a list of functions together with a "main" entrypoint
data Program v t = Program [StmtFun v t] v t
    deriving (Show, Eq)

-- | A program without type annotations
type UProgram = Program String ()

-- | A program with type annotations
type TProgram = Program String (Types String Int)


-- | Interpreter 

data IState = IState {
    fVars :: Map String (StmtFun String ()),
    bVars :: Map String Bool,
    pVars :: Map String Int,
    oVars :: Map String (CExpr String ()),
}

evalBExpr :: BExpr String () -> State IState Bool
evalBExpr (BConst b _) = return b
evalBExpr (BNot e _) = not <$> evalBExpr e
evalBExpr (BOp And e1 e2 _) = (&&) <$> evalBExpr e1 <*> evalBExpr e2
evalBExpr (BOp Or e1 e2 _) = (||) <$> evalBExpr e1 <*> evalBExpr e2
evalBExpr (BOp Impl e1 e2 _) = (||) <$> (not <$> evalBExpr e1) <*> evalBExpr e2
evalBExpr (BOp Iff e1 e2 _) = (==) <$> evalBExpr e1 <*> evalBExpr e2
evalBExpr (BComp Eq e1 e2 _) = (==) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BComp Neq e1 e2 _) = (/=) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BComp Lt e1 e2 _) = (<) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BComp Gt e1 e2 _) = (>) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BComp Leq e1 e2 _) = (<=) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BComp Geq e1 e2 _) = (>=) <$> evalPExpr e1 <*> evalPExpr e2
evalBExpr (BLitAt e1 e2 _) = (==) <$> e1 <*> evalPExpr e2
evalBExpr (BVar v _) = do
    bVars <- gets bVars
    case Map.lookup v bVars of
        Just b -> return b
        Nothing -> error $ "variable " ++ v ++ " not found"

evalPExpr :: PExpr String () -> State IState Int
evalPExpr (PFirst _) = return 0
evalPExpr (PVar v _) = do
    pVars <- gets pVars
    case Map.lookup v pVars of
        Just p -> return p
        Nothing -> error $ "variable " ++ v ++ " not found"

evalOExpr :: OExpr String () -> State IState (CExpr String ())
evalOExpr (OVar v _) = do
    oVars <- gets oVars
    case Map.lookup v oVars of
        Just c -> return c
        Nothing -> error $ "variable " ++ v ++ " not found"
evalOExpr (OList es _) = CList <$> mapM evalOExpr es
evalOExpr (ORev e _) = do
    CList es <- evalOExpr e
    return $ CList $ reverse es
evalOExpr (OFlat e _) = do
    CList es <- evalOExpr e
    return $ CList $ concatMap (\(CList es) -> es) es
evalOExpr (OIndex e1 e2 _) = do
    CList es <- evalOExpr e1
    i <- evalPExpr e2
    return $ es !! i
evalOExpr (OApp v es _) = do
    case Map.lookup v fVars of
        Just (StmtFun _ args body _) -> do
            -- todo
        Nothing -> error $ "function " ++ v ++ " not found"


evalStmt :: State IState (CExpr String ())
evalStmt (SIf cond t f _) = do
    b <- evalBExpr cond
    if b then evalStmt t else evalStmt f
evalStmt (SYield e _) = CList <$> evalOExpr e
evalStmt (SReturn e _) = evalOExpr e
evalStmt (SLet v e b _) = do
    c <- evalOExpr e
    modify $ \s -> s { oVars = Map.insert v c (oVars s) }
    evalStmt b
evalStmt (SSetTrue v _) = modify $ \s -> s { bVars = Map.insert v True (bVars s) }
evalStmt (SFor (i, v) x b _) = do
    CList es <- evalOExpr x
    forM_ (zip [0..] es) $ \(i, e) -> do
        modify $ \s -> s { pVars = Map.insert i (length es) (pVars s) }
        modify $ \s -> s { oVars = Map.insert i e (oVars s) }
        evalStmt b

evalStmtBlock :: StmtBlock String () -> State IState (CExpr String ())
evalStmtBlock (StmtBlock vars stmts _) = do
    modify $ \s -> s { bVars = Map.fromList (map (,False) vars) }
    modify $ \s -> s { pVars = Map.empty }
    modify $ \s -> s { oVars = Map.empty }
    forM_ stmts evalStmt



-- Now we parse a lisp-like language
-- coding our syntax.
--
-- We will use the following syntax:
-- 1. Boolean expressions : (and e1 e2), (or e1 e2), (not e), (impl e1 e2), (iff e1 e2) etc.
-- 2. Position expressions: (index e1 e2)
-- 3. Constant expressions: (char c), (c-list e1 e2 e3)
-- 4. Output expressions: (o-var v), (o-list e1 e2 e3), (o-rev e), (o-index e1 e2), (o-app v e1 e2 e3), etc.
-- 5. Statements: (if e1 s1 s2), (yield e), (return e), (let-o v e s), (let-b v e s), (set-true v), (for (i v) e s), etc.
-- 6. Function declarations: (def f ((v1 p1 p2 p3...) (v2) (v3 p1 p2 p3)) s), etc.
-- 7. Program: (program "main" (def f1 ((v1 p1 p2 p3...) (v2) (v3 p1 p2 p3)) s1) (def f2 ((v1 p1 p2 p3...) (v2) (v3 p1 p2 p3)) s2) ...)

type Parser = Parsec Void T.Text

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: T.Text -> Parser T.Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pChar :: Parser Char
pChar = between (char '\'') (char '\'') L.charLiteral

pList :: Parser a -> Parser [a]
pList p = parens (many p)

pVar :: Parser String
pVar = lexeme $ some letterChar

pBExpr :: Parser (BExpr String ())
pBExpr = choice
    [ parens $ do
        op <- choice
            [ And <$ symbol "and"
            , Or <$ symbol "or"
            , Impl <$ symbol "impl"
            , Iff <$ symbol "iff"
            ]
        e1 <- pBExpr
        e2 <- pBExpr
        return $ BOp op e1 e2 ()
    , parens $ do
        symbol "not"
        e <- pBExpr
        return $ BNot e ()
    , parens $ do
        comp <- choice
            [ Eq <$ symbol "eq"
            , Neq <$ symbol "neq"
            , Lt <$ symbol "lt"
            , Gt <$ symbol "gt"
            , Leq <$ symbol "leq"
            , Geq <$ symbol "geq"
            ]
        e1 <- pPExpr
        e2 <- pPExpr
        return $ BComp comp e1 e2 ()
    , parens $ do
        symbol "lit-at"
        e1 <- pCExpr
        e2 <- pPExpr
        return $ BLitAt e1 e2 ()
    , parens $ do
        symbol "app"
        v <- pVar
        es <- pList $ parens $ do
            e <- pOExpr
            ps <- pList pPExpr
            return (e, ps)
        return $ BApp v es ()
    , parens $ do
        v <- pVar
        return $ BVar v ()
    ]

pPExpr :: Parser (PExpr String ())
pPExpr = parens $ do
    v <- pVar
    return $ PVar v ()

pCExpr :: Parser (CExpr String ())
pCExpr = choice
    [ parens $ do
        symbol "char"
        c <- pChar
        return $ CChar c ()
    , parens $ do
        symbol "c-list"
        es <- pList pCExpr
        return $ CList es ()
    ]

pOExpr :: Parser (OExpr String ())
pOExpr = choice
    [ parens $ do
        symbol "o-var"
        v <- pVar
        return $ OVar v ()
    , parens $ do
        symbol "o-list"
        es <- pList pOExpr
        return $ OList es ()
    , parens $ do
        symbol "o-rev"
        e <- pOExpr
        return $ ORev e ()
    , parens $ do
        symbol "o-index"
        e1 <- pOExpr
        e2 <- pPExpr
        return $ OIndex e1 e2 ()
    , parens $ do
        symbol "o-app"
        v <- pVar
        es <- pList $ parens $ do
            e <- pOExpr
            ps <- pList pPExpr
            return (e, ps)
        return $ OApp v es ()
    , parens $ do
        symbol "o-gen"
        s <- pStmtBlock
        return $ OGen s ()
    ]

pStmt :: Parser (Stmt String ())
pStmt = choice
    [ parens $ do
        symbol "if"
        cond <- pBExpr
        t <- pStmtBlock
        f <- pStmtBlock
        return $ SIf cond t f ()
    , parens $ do
        symbol "yield"
        e <- pOExpr
        return $ SYield e ()
    , parens $ do
        symbol "return"
        e <- pOExpr
        return $ SReturn e ()
    , parens $ do
        symbol "let-o"
        v <- pVar
        e <- pOExpr
        b <- pStmtBlock
        return $ SLetOutput v e b ()
    , parens $ do
        symbol "let-b"
        vs <- pList pVar
        b <- pStmtBlock
        return $ SLetBoolean vs b ()
    , parens $ do
        symbol "set-true"
        v <- pVar
        return $ SSetTrue v ()
    , parens $ do
        symbol "for"
        parens $ do
            i <- pVar
            v <- pVar
        e <- pOExpr
        b <- pStmtBlock
        return $ SFor (i, v) e b ()
    ]

pStmtBlock :: Parser (StmtBlock String ())
pStmtBlock = parens $ do
    vars <- pList pVar
    stmts <- many pStmt
    return $ StmtBlock vars stmts ()

pStmtFun :: Parser (StmtFun String ())
pStmtFun = parens $ do
    symbol "def"
    f <- pVar
    args <- pList $ parens $ do
        v <- pVar
        ps <- many pVar
        return (v, ps)
    b <- pStmtBlock
    return $ StmtFun f args b ()

pProgram :: Parser UProgram
pProgram = parens $ do
    symbol "program"
    f <- pVar
    fs <- many pStmtFun
    return $ Program fs f ()

parseProgram :: T.Text -> Either (ParseErrorBundle T.Text Void) UProgram
parseProgram = parse pProgram ""

-- | Example program
example :: T.Text
example = "(program main (def main ((w)) ((for (i v) (o-rev w) (yield (o-var v))))))"

