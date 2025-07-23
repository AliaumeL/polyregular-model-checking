module ForPrograms.HighLevel.Transformations.FinalConditions where 

import ForPrograms.HighLevel

-- 1. The program does not contain any generator expressions.

noGenerators :: Program s t -> Bool 
noGenerators (Program fs main) = all noGeneratorsFun fs

noGeneratorsFun :: StmtFun s t -> Bool
noGeneratorsFun (StmtFun _ args s t) = noGeneratorsStmt s

noGeneratorsStmt :: Stmt s t -> Bool
noGeneratorsStmt (SIf b s1 s2 _) = noGeneratorsBExpr b && noGeneratorsStmt s1 && noGeneratorsStmt s2 
noGeneratorsStmt (SYield e _) = noGeneratorsOExpr e
noGeneratorsStmt (SOReturn e _) = noGeneratorsOExpr e
noGeneratorsStmt (SBReturn b _) = noGeneratorsBExpr b
noGeneratorsStmt (SLetOutput _ e s _) = noGeneratorsOExpr e && noGeneratorsStmt s
noGeneratorsStmt (SSetTrue _ _) = True
noGeneratorsStmt (SFor _ _ e s _) = noGeneratorsOExpr e && noGeneratorsStmt s
noGeneratorsStmt (SSeq ss _) = all noGeneratorsStmt ss
noGeneratorsStmt (SLetBoolean _ s _) = noGeneratorsStmt s

noGeneratorsOExpr :: OExpr s t -> Bool
noGeneratorsOExpr (OVar _ _) = True
noGeneratorsOExpr (OConst _ _) = True
noGeneratorsOExpr (OList _ _) = True
noGeneratorsOExpr (OApp _ args _) = all noGeneratorsOExpr (map fst args)
noGeneratorsOExpr (OGen _ _) = False

noGeneratorsBExpr :: BExpr s t -> Bool
noGeneratorsBExpr (BConst _ _) = True
noGeneratorsBExpr (BNot b _) = noGeneratorsBExpr b
noGeneratorsBExpr (BOp _ b1 b2 _) = noGeneratorsBExpr b1 && noGeneratorsBExpr b2
noGeneratorsBExpr (BComp _ e1 e2 _) = True 
noGeneratorsBExpr (BVar _ _) = True
noGeneratorsBExpr (BGen _ _) = False
noGeneratorsBExpr (BApp _ args _) = all noGeneratorsOExpr (map fst args)
noGeneratorsBExpr (BLitEq _ c e _) = noGeneratorsOExpr e


-- 2. The program does not contain any let x = in y expression. 
-- This does not include boolean variables, which are allowed.

noOLets :: Program s t -> Bool
noOLets (Program fs main) = all noOLetsFun fs

noOLetsFun :: StmtFun s t -> Bool
noOLetsFun (StmtFun _ args s t) = noOLetsStmt s

noOLetsStmt :: Stmt s t -> Bool
noOLetsStmt (SIf b s1 s2 _) = noOLetsBExpr b && noOLetsStmt s1 && noOLetsStmt s2
noOLetsStmt (SYield e _) = noOLetsOExpr e
noOLetsStmt (SOReturn e _) = noOLetsOExpr e
noOLetsStmt (SBReturn b _) = noOLetsBExpr b
noOLetsStmt (SLetOutput _ e s _) = False
noOLetsStmt (SLetBoolean _ s _) = noOLetsStmt s
noOLetsStmt (SSetTrue _ _) = True
noOLetsStmt (SFor _ _ e s _) = noOLetsOExpr e && noOLetsStmt s
noOLetsStmt (SSeq ss _) = all noOLetsStmt ss

noOLetsOExpr :: OExpr s t -> Bool
noOLetsOExpr (OVar _ _) = True
noOLetsOExpr (OConst _ _) = True
noOLetsOExpr (OList es _) = all noOLetsOExpr es
noOLetsOExpr (OApp _ args _) = all noOLetsOExpr (map fst args)
noOLetsOExpr (OGen stmt _) = noOLetsStmt stmt

noOLetsBExpr :: BExpr s t -> Bool
noOLetsBExpr (BConst _ _) = True
noOLetsBExpr (BNot b _) = noOLetsBExpr b
noOLetsBExpr (BOp _ b1 b2 _) = noOLetsBExpr b1 && noOLetsBExpr b2
noOLetsBExpr (BComp _ e1 e2 _) = True
noOLetsBExpr (BVar _ _) = True
noOLetsBExpr (BGen stmt _) = noOLetsStmt stmt
noOLetsBExpr (BApp _ args _) = all noOLetsOExpr (map fst args)
noOLetsBExpr (BLitEq _ c e _) = noOLetsOExpr e

-- 3. All for loops iterate over variables only.

forLoopsOverOnlyVars :: Program s t -> Bool
forLoopsOverOnlyVars (Program fs main) = all forLoopsOverOnlyVarsFun fs

forLoopsOverOnlyVarsFun :: StmtFun s t -> Bool
forLoopsOverOnlyVarsFun (StmtFun _ args s t) = forLoopsOverOnlyVarsStmt s

forLoopsOverOnlyVarsStmt :: Stmt s t -> Bool
forLoopsOverOnlyVarsStmt (SIf b s1 s2 _) = forLoopsOverOnlyVarsBExpr b && forLoopsOverOnlyVarsStmt s1 && forLoopsOverOnlyVarsStmt s2
forLoopsOverOnlyVarsStmt (SYield e _) = forLoopsOverOnlyVarsOExpr e
forLoopsOverOnlyVarsStmt (SOReturn e _) = forLoopsOverOnlyVarsOExpr e
forLoopsOverOnlyVarsStmt (SBReturn b _) = forLoopsOverOnlyVarsBExpr b
forLoopsOverOnlyVarsStmt (SLetOutput _ e s _) = forLoopsOverOnlyVarsOExpr e && forLoopsOverOnlyVarsStmt s
forLoopsOverOnlyVarsStmt (SLetBoolean _ s _) = forLoopsOverOnlyVarsStmt s
forLoopsOverOnlyVarsStmt (SSetTrue _ _) = True
forLoopsOverOnlyVarsStmt (SFor _ (i, v, _) (OVar _ _) s _) = forLoopsOverOnlyVarsStmt s
forLoopsOverOnlyVarsStmt (SFor _ (i, v, _) e s _) = False
forLoopsOverOnlyVarsStmt (SSeq ss _) = all forLoopsOverOnlyVarsStmt ss

forLoopsOverOnlyVarsOExpr :: OExpr s t -> Bool
forLoopsOverOnlyVarsOExpr (OVar _ _) = True
forLoopsOverOnlyVarsOExpr (OConst _ _) = True
forLoopsOverOnlyVarsOExpr (OList es _) = all forLoopsOverOnlyVarsOExpr es
forLoopsOverOnlyVarsOExpr (OApp _ args _) = all forLoopsOverOnlyVarsOExpr (map fst args)
forLoopsOverOnlyVarsOExpr (OGen stmt _) = forLoopsOverOnlyVarsStmt stmt

forLoopsOverOnlyVarsBExpr :: BExpr s t -> Bool
forLoopsOverOnlyVarsBExpr (BConst _ _) = True
forLoopsOverOnlyVarsBExpr (BNot b _) = forLoopsOverOnlyVarsBExpr b
forLoopsOverOnlyVarsBExpr (BOp _ b1 b2 _) = forLoopsOverOnlyVarsBExpr b1 && forLoopsOverOnlyVarsBExpr b2
forLoopsOverOnlyVarsBExpr (BComp _ e1 e2 _) = True
forLoopsOverOnlyVarsBExpr (BVar _ _) = True
forLoopsOverOnlyVarsBExpr (BGen stmt _) = forLoopsOverOnlyVarsStmt stmt
forLoopsOverOnlyVarsBExpr (BApp _ args _) = all forLoopsOverOnlyVarsOExpr (map fst args)
forLoopsOverOnlyVarsBExpr (BLitEq _ c e _) = forLoopsOverOnlyVarsOExpr e

-- 4. There are no return statements (either output or boolean).
noReturnStmts :: Program s t -> Bool
noReturnStmts (Program fs main) = all noReturnStmtsFun fs

noReturnStmtsFun :: StmtFun s t -> Bool
noReturnStmtsFun (StmtFun _ args s t) = noReturnStmtsStmt s

noReturnStmtsStmt :: Stmt s t -> Bool
noReturnStmtsStmt (SIf b s1 s2 _) = noReturnStmtsBExpr b && noReturnStmtsStmt s1 && noReturnStmtsStmt s2
noReturnStmtsStmt (SYield e _) = noReturnStmtsOExpr e
noReturnStmtsStmt (SOReturn e _) = False
noReturnStmtsStmt (SBReturn b _) = False
noReturnStmtsStmt (SLetOutput _ e s _) = noReturnStmtsOExpr e && noReturnStmtsStmt s
noReturnStmtsStmt (SLetBoolean _ s _) = noReturnStmtsStmt s
noReturnStmtsStmt (SSetTrue _ _) = True
noReturnStmtsStmt (SFor _ (i, v, _) e s _) = noReturnStmtsOExpr e && noReturnStmtsStmt s
noReturnStmtsStmt (SSeq ss _) = all noReturnStmtsStmt ss

noReturnStmtsOExpr :: OExpr s t -> Bool
noReturnStmtsOExpr (OVar _ _) = True
noReturnStmtsOExpr (OConst _ _) = True
noReturnStmtsOExpr (OList es _) = all noReturnStmtsOExpr es
noReturnStmtsOExpr (OApp _ args _) = all noReturnStmtsOExpr (map fst args)
noReturnStmtsOExpr (OGen stmt _) = noReturnStmtsStmt stmt

noReturnStmtsBExpr :: BExpr s t -> Bool
noReturnStmtsBExpr (BConst _ _) = True
noReturnStmtsBExpr (BNot b _) = noReturnStmtsBExpr b
noReturnStmtsBExpr (BOp _ b1 b2 _) = noReturnStmtsBExpr b1 && noReturnStmtsBExpr b2
noReturnStmtsBExpr (BComp _ e1 e2 _) = True
noReturnStmtsBExpr (BVar _ _) = True
noReturnStmtsBExpr (BGen stmt _) = noReturnStmtsStmt stmt
noReturnStmtsBExpr (BApp _ args _) = all noReturnStmtsOExpr (map fst args)
noReturnStmtsBExpr (BLitEq _ c e _) = noReturnStmtsOExpr e

-- 5. All BLitEq are for the form 'c' == x, where c is a character constant and x is a variable.

allBLitEqForm :: Program s t -> Bool
allBLitEqForm (Program fs main) = all allBLitEqFormFun fs

allBLitEqFormFun :: StmtFun s t -> Bool
allBLitEqFormFun (StmtFun _ args s t) = allBLitEqFormStmt s

allBLitEqFormStmt :: Stmt s t -> Bool
allBLitEqFormStmt (SIf b s1 s2 _) = allBLitEqFormBExpr b && allBLitEqFormStmt s1 && allBLitEqFormStmt s2
allBLitEqFormStmt (SYield e _) = allBLitEqFormOExpr e
allBLitEqFormStmt (SOReturn e _) = allBLitEqFormOExpr e
allBLitEqFormStmt (SBReturn b _) = allBLitEqFormBExpr b
allBLitEqFormStmt (SLetOutput _ e s _) = allBLitEqFormOExpr e && allBLitEqFormStmt s
allBLitEqFormStmt (SLetBoolean _ s _) = allBLitEqFormStmt s
allBLitEqFormStmt (SSetTrue _ _) = True
allBLitEqFormStmt (SFor _ (i, v, _) e s _) = allBLitEqFormOExpr e && allBLitEqFormStmt s
allBLitEqFormStmt (SSeq ss _) = all allBLitEqFormStmt ss
allBLitEqFormStmt (SLetBoolean _ s _) = allBLitEqFormStmt s

allBLitEqFormOExpr :: OExpr s t -> Bool
allBLitEqFormOExpr (OVar _ _) = True
allBLitEqFormOExpr (OConst _ _) = True
allBLitEqFormOExpr (OList es _) = all allBLitEqFormOExpr es
allBLitEqFormOExpr (OApp _ args _) = all allBLitEqFormOExpr (map fst args)
allBLitEqFormOExpr (OGen stmt _) = allBLitEqFormStmt stmt

allBLitEqFormBExpr :: BExpr s t -> Bool
allBLitEqFormBExpr (BConst _ _) = True
allBLitEqFormBExpr (BNot b _) = allBLitEqFormBExpr b
allBLitEqFormBExpr (BOp _ b1 b2 _) = allBLitEqFormBExpr b1 && allBLitEqFormBExpr b2
allBLitEqFormBExpr (BComp _ e1 e2 _) = True
allBLitEqFormBExpr (BVar _ _) = True
allBLitEqFormBExpr (BGen stmt _) = allBLitEqFormStmt stmt
allBLitEqFormBExpr (BApp _ args _) = all allBLitEqFormOExpr (map fst args)
allBLitEqFormBExpr (BLitEq _ (CChar _ _) (OVar _ _) _) = True
allBLitEqFormBExpr _ = False

-- 6. All boolean variables are declared either at the beginning of the function or at the beginning of the program.
allBVarsAtBeginningScope :: Program s t -> Bool
allBVarsAtBeginningScope (Program fs main) = all allBVarsAtBeginningScopeFun fs

allBVarsAtBeginningScopeFun :: StmtFun s t -> Bool
allBVarsAtBeginningScopeFun (StmtFun _ args s t) = allBVarsAtBeginningScopeStmt s

allBVarsAtBeginningScopeStmt :: Stmt s t -> Bool
allBVarsAtBeginningScopeStmt (SLetBoolean _ s _) = allBVarsAtBeginningScopeStmt s
allBVarsAtBeginningScopeStmt x = noLetBVars x 

noLetBVars :: Stmt s t -> Bool
noLetBVars (SIf b s1 s2 _) = noLetBVarsBExpr b && noLetBVars s1 && noLetBVars s2
noLetBVars (SYield e _) = noLetBVarsOExpr e
noLetBVars (SOReturn e _) = noLetBVarsOExpr e
noLetBVars (SBReturn b _) = noLetBVarsBExpr b
noLetBVars (SLetOutput _ e s _) = noLetBVarsOExpr e && noLetBVars s
noLetBVars (SLetBoolean _ s _) = False 
noLetBVars (SSetTrue _ _) = True
noLetBVars (SFor _ (i, v, _) e s _) = noLetBVarsOExpr e && allBVarsAtBeginningScopeStmt s
noLetBVars (SSeq ss _) = all noLetBVars ss

noLetBVarsOExpr :: OExpr s t -> Bool
noLetBVarsOExpr (OVar _ _) = True
noLetBVarsOExpr (OConst _ _) = True
noLetBVarsOExpr (OList es _) = all noLetBVarsOExpr es
noLetBVarsOExpr (OApp _ args _) = all noLetBVarsOExpr (map fst args)
noLetBVarsOExpr (OGen stmt _) = noLetBVars stmt

noLetBVarsBExpr :: BExpr s t -> Bool
noLetBVarsBExpr (BConst _ _) = True
noLetBVarsBExpr (BNot b _) = noLetBVarsBExpr b
noLetBVarsBExpr (BOp _ b1 b2 _) = noLetBVarsBExpr b1 && noLetBVarsBExpr b2
noLetBVarsBExpr (BComp _ e1 e2 _) = True
noLetBVarsBExpr (BVar _ _) = True
noLetBVarsBExpr (BGen stmt _) = noLetBVars stmt
noLetBVarsBExpr (BApp _ args _) = all noLetBVarsOExpr (map fst args)
noLetBVarsBExpr (BLitEq _ c e _) = noLetBVarsOExpr e

-- Now we combine all the conditions into one function that checks all of them.

finalConditions :: Program s t -> Bool
finalConditions p = noGenerators p && noOLets p && forLoopsOverOnlyVars p && noReturnStmts p && allBLitEqForm p && allBVarsAtBeginningScope p

-- Also we want a function that displays a list of all the conditions that are not met.
conditionsWithNames :: [(Program s t -> Bool, String)]
conditionsWithNames = [(noGenerators, "No generators"), (noOLets, "No let x = in y"), (forLoopsOverOnlyVars, "For loops over only variables"), (noReturnStmts, "No return statements"), (allBLitEqForm, "All BLitEq are for the form 'c' == x"), (allBVarsAtBeginningScope, "All boolean variables are declared at the beginning of the function or at the beginning of the program")]

displayBrokenConditions :: Program s t -> String 
displayBrokenConditions p = unlines [name | (cond, name) <- conditionsWithNames, not (cond p)]
