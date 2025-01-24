module Parser.ParsedToFirstOrderLogic where

import qualified Parser.FirstOrderLogic.Abs as P
import Logic.Formulas 
import Logic.QuantifierFree

capture :: String -> Formula String  -> Formula String
capture name f = quantInVars fun f
  where 
    fun _ x | x == name = Just (In x)
    fun _ _ = Nothing

parsedToFirstOrderLogic :: P.Formula -> Formula String
parsedToFirstOrderLogic (P.FQuant (P.QuantForall (P.Ident ident) t) f) = FQuant Forall ident (parseType t) $ capture ident (parsedToFirstOrderLogic f)
parsedToFirstOrderLogic (P.FQuant (P.QuantExists (P.Ident ident) t) f) = FQuant Exists ident (parseType t) $ capture ident (parsedToFirstOrderLogic f)
parsedToFirstOrderLogic (P.FIff f1 f2) = FBin Equiv  (parsedToFirstOrderLogic f1) (parsedToFirstOrderLogic f2)
parsedToFirstOrderLogic (P.FImpl f1 f2) = FBin Impl  (parsedToFirstOrderLogic f1) (parsedToFirstOrderLogic f2)
parsedToFirstOrderLogic (P.FAnd f1 f2) = FBin Conj  (parsedToFirstOrderLogic f1) (parsedToFirstOrderLogic f2)
parsedToFirstOrderLogic (P.FOr f1 f2) = FBin Disj  (parsedToFirstOrderLogic f1) (parsedToFirstOrderLogic f2)
parsedToFirstOrderLogic (P.FNot f) = FNot (parsedToFirstOrderLogic f)
parsedToFirstOrderLogic P.FTrue = FConst True
parsedToFirstOrderLogic P.FFalse = FConst False
parsedToFirstOrderLogic (P.FAtom p) = predicateToFormula p

predicateToFormula :: P.Predicate -> Formula String
predicateToFormula (P.BoolVar (P.Ident ident)) =
    FVar (In ident)
predicateToFormula (P.BinTest (P.Ident ident1) op (P.Ident ident2)) =
    FTestPos (testOpToBinOp op) (In ident1) (In ident2)
predicateToFormula (P.BinLetEq (P.Ident ident) c) =
    FLetter (In ident) c
predicateToFormula (P.BinTagEq (P.Ident ident) s) =
    FTag (In ident) s

parseType :: P.Type -> Sort 
parseType P.TPos = Pos
parseType P.TBool = Boolean
parseType P.TTag = Tag

testOpToBinOp :: P.TestOp -> TestOp
testOpToBinOp P.TLe = Le
testOpToBinOp P.TLt = Lt
testOpToBinOp P.TGe = Ge
testOpToBinOp P.TGt = Gt
testOpToBinOp P.TEq = Eq
testOpToBinOp P.TNeq = Neq
