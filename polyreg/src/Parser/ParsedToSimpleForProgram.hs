module Parser.ParsedToSimpleForProgram where

import qualified Parser.SimpleForProgram.Abs as P 
import qualified ForPrograms.Simple as T 
import Logic.QuantifierFree (TestOp(..), BinOp(..)) 

parsedToForProgram :: P.Program -> T.ForProgram
parsedToForProgram (P.Program (P.VarStmt vars stmt)) = T.ForProgram (map identToBName vars) $ stmtListToStmt stmt 

identToBName :: P.Ident -> T.BName
identToBName (P.Ident s) = T.BName s

identToPName :: P.Ident -> T.PName
identToPName (P.Ident s) = T.PName s

getVars :: P.VarStmt -> [T.BName]
getVars (P.VarStmt vars _) = map identToBName vars
getVars (P.NoVarStmt _) = []

stmtListToStmt :: [P.Stmt] -> T.ForStmt
stmtListToStmt [x] = parsedToStmt x
stmtListToStmt stmts = T.Seq $ map parsedToStmt stmts

varStmtToStmt :: P.VarStmt -> T.ForStmt
varStmtToStmt (P.VarStmt _ stmts) = stmtListToStmt stmts
varStmtToStmt (P.NoVarStmt stmts) = stmtListToStmt stmts

parsedToDir :: P.FORInput -> T.Direction
parsedToDir P.FInput = T.LeftToRight 
parsedToDir P.FRevInput = T.RightToLeft

parsedToStmt :: P.Stmt -> T.ForStmt
parsedToStmt (P.SFor var l stmt) = T.For (identToPName var) (parsedToDir l) (getVars stmt) (varStmtToStmt stmt)
parsedToStmt (P.SIfElse b s1 s2) = T.If (parsedToBExpr b) (stmtListToStmt s1) (stmtListToStmt s2)
parsedToStmt (P.SIf b s) = T.If (parsedToBExpr b) (stmtListToStmt s) (T.Seq [])
parsedToStmt (P.SSetTrue var) = T.SetTrue (identToBName var)
parsedToStmt (P.SPrintChar c) = T.PrintLbl c
parsedToStmt (P.SPrintLabel p) = T.PrintPos (identToPName p)

parsedToBExpr :: P.BExpr -> T.BoolExpr
parsedToBExpr (P.BTrue) = T.BConst True 
parsedToBExpr (P.BFalse) = T.BConst False
parsedToBExpr (P.BVar v) = T.BVar $ identToBName v
parsedToBExpr (P.BNot b) = T.BNot $ parsedToBExpr b
parsedToBExpr (P.BTest p1 op p2) = T.BTest (parsedToBTest op) (identToPName p1) (identToPName p2)
parsedToBExpr (P.BLabelAt l c) = T.BLabelAt (identToPName l) c
parsedToBExpr (P.BAnd e1 e2) = T.BBin Conj (parsedToBExpr e1) (parsedToBExpr e2)
parsedToBExpr (P.BOr e1 e2) = T.BBin Disj (parsedToBExpr e1) (parsedToBExpr e2) 

parsedToBTest :: P.BTest -> TestOp
parsedToBTest P.TLe = Le 
parsedToBTest P.TLt = Lt 
parsedToBTest P.TGe = Ge 
parsedToBTest P.TGt = Gt 
parsedToBTest P.TEq = Eq 
parsedToBTest P.TNeq = Neq
