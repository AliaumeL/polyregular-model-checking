-- File generated by the BNF Converter (bnfc 2.9.5).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for Parser.

module Parser.HighLevelForProgram.Print where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified Parser.HighLevelForProgram.Abs

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t, null spc, null rest) of
      (True , _   , True ) -> []             -- remove trailing space
      (False, _   , True ) -> t              -- remove trailing space
      (False, True, False) -> t ++ ' ' : s   -- add space if none
      _                    -> t ++ s
    where
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Parser.HighLevelForProgram.Abs.Ident where
  prt _ (Parser.HighLevelForProgram.Abs.Ident i) = doc $ showString i
instance Print Parser.HighLevelForProgram.Abs.Program where
  prt i = \case
    Parser.HighLevelForProgram.Abs.ProgramC funcs -> prPrec i 0 (concatD [prt 0 funcs])

instance Print [Parser.HighLevelForProgram.Abs.Func] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print Parser.HighLevelForProgram.Abs.Func where
  prt i = \case
    Parser.HighLevelForProgram.Abs.FuncC id_ argds type_ stmts -> prPrec i 0 (concatD [doc (showString "def"), prt 0 id_, doc (showString "("), prt 0 argds, doc (showString ")"), doc (showString ":"), prt 0 type_, doc (showString ":="), prt 0 stmts])

instance Print Parser.HighLevelForProgram.Abs.Stmt where
  prt i = \case
    Parser.HighLevelForProgram.Abs.SFor id_1 id_2 expr stmts -> prPrec i 0 (concatD [doc (showString "for"), doc (showString "("), prt 0 id_1, doc (showString ","), prt 0 id_2, doc (showString ")"), doc (showString "in"), doc (showString "enumerate"), doc (showString "("), prt 0 expr, doc (showString ")"), doc (showString "do"), prt 0 stmts, doc (showString "done")])
    Parser.HighLevelForProgram.Abs.SRFor id_1 id_2 expr stmts -> prPrec i 0 (concatD [doc (showString "for"), doc (showString "("), prt 0 id_1, doc (showString ","), prt 0 id_2, doc (showString ")"), doc (showString "in"), doc (showString "reversed"), doc (showString "("), doc (showString "enumerate"), doc (showString "("), prt 0 expr, doc (showString ")"), doc (showString ")"), doc (showString "do"), prt 0 stmts, doc (showString "done")])
    Parser.HighLevelForProgram.Abs.SIf expr stmts -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expr, doc (showString "then"), prt 0 stmts, doc (showString "endif")])
    Parser.HighLevelForProgram.Abs.SIfE expr stmts1 stmts2 -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expr, doc (showString "then"), prt 0 stmts1, doc (showString "else"), prt 0 stmts2, doc (showString "endif")])
    Parser.HighLevelForProgram.Abs.SYield expr -> prPrec i 0 (concatD [doc (showString "yield"), prt 0 expr])
    Parser.HighLevelForProgram.Abs.SReturn expr -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expr])
    Parser.HighLevelForProgram.Abs.SLetIn id_ expr stmts -> prPrec i 0 (concatD [doc (showString "let"), prt 0 id_, doc (showString ":="), prt 0 expr, doc (showString "in"), prt 0 stmts])
    Parser.HighLevelForProgram.Abs.SLetBIn id_ stmts -> prPrec i 0 (concatD [doc (showString "let"), doc (showString "mut"), prt 0 id_, doc (showString ":="), doc (showString "False"), doc (showString "in"), prt 0 stmts])
    Parser.HighLevelForProgram.Abs.SLetSetTrue id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":="), doc (showString "True")])

instance Print [Parser.HighLevelForProgram.Abs.Stmt] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print Parser.HighLevelForProgram.Abs.Expr where
  prt i = \case
    Parser.HighLevelForProgram.Abs.VEChar c -> prPrec i 3 (concatD [prt 0 c])
    Parser.HighLevelForProgram.Abs.VEString str -> prPrec i 3 (concatD [printString str])
    Parser.HighLevelForProgram.Abs.VEListConstr exprs -> prPrec i 3 (concatD [doc (showString "["), prt 0 exprs, doc (showString "]")])
    Parser.HighLevelForProgram.Abs.VEGen stmts -> prPrec i 3 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "}")])
    Parser.HighLevelForProgram.Abs.VEVal id_ -> prPrec i 3 (concatD [prt 0 id_])
    Parser.HighLevelForProgram.Abs.VEFunc id_ veargs -> prPrec i 3 (concatD [prt 0 id_, doc (showString "("), prt 0 veargs, doc (showString ")")])
    Parser.HighLevelForProgram.Abs.BETrue -> prPrec i 3 (concatD [doc (showString "True")])
    Parser.HighLevelForProgram.Abs.BEFalse -> prPrec i 3 (concatD [doc (showString "False")])
    Parser.HighLevelForProgram.Abs.BENot expr -> prPrec i 3 (concatD [doc (showString "not"), prt 3 expr])
    Parser.HighLevelForProgram.Abs.BEBinOp expr1 binop expr2 -> prPrec i 2 (concatD [prt 3 expr1, prt 0 binop, prt 3 expr2])
    Parser.HighLevelForProgram.Abs.BEAnd expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "and"), prt 1 expr2])
    Parser.HighLevelForProgram.Abs.BEOr expr1 expr2 -> prPrec i 0 (concatD [prt 1 expr1, doc (showString "or"), prt 0 expr2])

instance Print [Parser.HighLevelForProgram.Abs.Expr] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Parser.HighLevelForProgram.Abs.Type where
  prt i = \case
    Parser.HighLevelForProgram.Abs.TChar -> prPrec i 1 (concatD [doc (showString "Char")])
    Parser.HighLevelForProgram.Abs.TList type_ -> prPrec i 1 (concatD [doc (showString "["), prt 0 type_, doc (showString "]")])
    Parser.HighLevelForProgram.Abs.TBool -> prPrec i 2 (concatD [doc (showString "Bool")])

instance Print Parser.HighLevelForProgram.Abs.VEArg where
  prt i = \case
    Parser.HighLevelForProgram.Abs.VEArgSole expr -> prPrec i 0 (concatD [prt 0 expr])
    Parser.HighLevelForProgram.Abs.VEArgWithPoses expr ids -> prPrec i 0 (concatD [prt 0 expr, doc (showString "with"), doc (showString "("), prt 0 ids, doc (showString ")")])

instance Print [Parser.HighLevelForProgram.Abs.Ident] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Parser.HighLevelForProgram.Abs.VEArg] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Parser.HighLevelForProgram.Abs.ArgD where
  prt i = \case
    Parser.HighLevelForProgram.Abs.ArgDSole id_ type_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 type_])
    Parser.HighLevelForProgram.Abs.ArgDWithPoses id_ type_ ids -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 type_, doc (showString "with"), doc (showString "("), prt 0 ids, doc (showString ")")])

instance Print [Parser.HighLevelForProgram.Abs.ArgD] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Parser.HighLevelForProgram.Abs.BinOp where
  prt i = \case
    Parser.HighLevelForProgram.Abs.BinOpEq -> prPrec i 0 (concatD [doc (showString "=")])
    Parser.HighLevelForProgram.Abs.BinOpNeq -> prPrec i 0 (concatD [doc (showString "!=")])
    Parser.HighLevelForProgram.Abs.BinOpLeq -> prPrec i 0 (concatD [doc (showString "<=")])
    Parser.HighLevelForProgram.Abs.BinOpLt -> prPrec i 0 (concatD [doc (showString "<")])
    Parser.HighLevelForProgram.Abs.BinOpGeq -> prPrec i 0 (concatD [doc (showString ">=")])
    Parser.HighLevelForProgram.Abs.BinOpGt -> prPrec i 0 (concatD [doc (showString ">")])
    Parser.HighLevelForProgram.Abs.BinOpVEqT type_ -> prPrec i 0 (concatD [doc (showString "="), prt 0 type_, doc (showString "=")])
    Parser.HighLevelForProgram.Abs.BinOpVEq -> prPrec i 0 (concatD [doc (showString "===")])
    Parser.HighLevelForProgram.Abs.BinOpVNe -> prPrec i 0 (concatD [doc (showString "!==")])
