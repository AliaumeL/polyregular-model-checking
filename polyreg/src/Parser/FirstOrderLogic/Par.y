-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Parser.FirstOrderLogic.Par
  ( happyError
  , myLexer
  , pFormula
  , pFormula1
  , pFormula2
  , pFormula3
  , pFormula4
  , pFormula5
  , pQuantifier
  , pType
  , pPredicate
  , pTestOp
  ) where

import Prelude

import qualified Parser.FirstOrderLogic.Abs
import Parser.FirstOrderLogic.Lex

}

%name pFormula Formula
%name pFormula1 Formula1
%name pFormula2 Formula2
%name pFormula3 Formula3
%name pFormula4 Formula4
%name pFormula5 Formula5
%name pQuantifier Quantifier
%name pType Type
%name pPredicate Predicate
%name pTestOp TestOp
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!='     { PT _ (TS _ 1)  }
  '('      { PT _ (TS _ 2)  }
  ')'      { PT _ (TS _ 3)  }
  '.'      { PT _ (TS _ 4)  }
  ':'      { PT _ (TS _ 5)  }
  '<'      { PT _ (TS _ 6)  }
  '<='     { PT _ (TS _ 7)  }
  '='      { PT _ (TS _ 8)  }
  '>'      { PT _ (TS _ 9)  }
  '>='     { PT _ (TS _ 10) }
  'Bool'   { PT _ (TS _ 11) }
  'Pos'    { PT _ (TS _ 12) }
  'Tag'    { PT _ (TS _ 13) }
  'false'  { PT _ (TS _ 14) }
  'true'   { PT _ (TS _ 15) }
  '¬'      { PT _ (TS _ 16) }
  '→'      { PT _ (TS _ 17) }
  '↔'      { PT _ (TS _ 18) }
  '∀'      { PT _ (TS _ 19) }
  '∃'      { PT _ (TS _ 20) }
  '∧'      { PT _ (TS _ 21) }
  '∨'      { PT _ (TS _ 22) }
  L_Ident  { PT _ (TV $$)   }
  L_charac { PT _ (TC $$)   }
  L_quoted { PT _ (TL $$)   }

%%

Ident :: { Parser.FirstOrderLogic.Abs.Ident }
Ident  : L_Ident { Parser.FirstOrderLogic.Abs.Ident $1 }

Char    :: { Char }
Char     : L_charac { (read $1) :: Char }

String  :: { String }
String   : L_quoted { $1 }

Formula :: { Parser.FirstOrderLogic.Abs.Formula }
Formula
  : Quantifier Formula1 { Parser.FirstOrderLogic.Abs.FQuant $1 $2 }
  | Formula1 { $1 }

Formula1 :: { Parser.FirstOrderLogic.Abs.Formula }
Formula1
  : Formula2 '↔' Formula1 { Parser.FirstOrderLogic.Abs.FIff $1 $3 }
  | Formula2 { $1 }

Formula2 :: { Parser.FirstOrderLogic.Abs.Formula }
Formula2
  : Formula3 '→' Formula2 { Parser.FirstOrderLogic.Abs.FImpl $1 $3 }
  | Formula3 { $1 }

Formula3 :: { Parser.FirstOrderLogic.Abs.Formula }
Formula3
  : Formula4 '∧' Formula3 { Parser.FirstOrderLogic.Abs.FAnd $1 $3 }
  | Formula4 { $1 }

Formula4 :: { Parser.FirstOrderLogic.Abs.Formula }
Formula4
  : Formula5 '∨' Formula4 { Parser.FirstOrderLogic.Abs.FOr $1 $3 }
  | Formula5 { $1 }

Formula5 :: { Parser.FirstOrderLogic.Abs.Formula }
Formula5
  : '¬' Formula5 { Parser.FirstOrderLogic.Abs.FNot $2 }
  | 'true' { Parser.FirstOrderLogic.Abs.FTrue }
  | 'false' { Parser.FirstOrderLogic.Abs.FFalse }
  | Predicate { Parser.FirstOrderLogic.Abs.FAtom $1 }
  | '(' Formula ')' { $2 }

Quantifier :: { Parser.FirstOrderLogic.Abs.Quantifier }
Quantifier
  : '∀' Ident ':' Type '.' { Parser.FirstOrderLogic.Abs.QuantForall $2 $4 }
  | '∃' Ident ':' Type '.' { Parser.FirstOrderLogic.Abs.QuantExists $2 $4 }

Type :: { Parser.FirstOrderLogic.Abs.Type }
Type
  : 'Pos' { Parser.FirstOrderLogic.Abs.TPos }
  | 'Bool' { Parser.FirstOrderLogic.Abs.TBool }
  | 'Tag' { Parser.FirstOrderLogic.Abs.TTag }

Predicate :: { Parser.FirstOrderLogic.Abs.Predicate }
Predicate
  : Ident { Parser.FirstOrderLogic.Abs.BoolVar $1 }
  | Ident TestOp Ident { Parser.FirstOrderLogic.Abs.BinTest $1 $2 $3 }
  | Ident '=' Char { Parser.FirstOrderLogic.Abs.BinLetEq $1 $3 }
  | Ident '=' String { Parser.FirstOrderLogic.Abs.BinTagEq $1 $3 }

TestOp :: { Parser.FirstOrderLogic.Abs.TestOp }
TestOp
  : '<=' { Parser.FirstOrderLogic.Abs.TLe }
  | '<' { Parser.FirstOrderLogic.Abs.TLt }
  | '>=' { Parser.FirstOrderLogic.Abs.TGe }
  | '>' { Parser.FirstOrderLogic.Abs.TGt }
  | '=' { Parser.FirstOrderLogic.Abs.TEq }
  | '!=' { Parser.FirstOrderLogic.Abs.TNeq }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

}

