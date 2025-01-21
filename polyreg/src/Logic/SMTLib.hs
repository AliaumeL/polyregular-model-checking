{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.SMTLib where

import QuantifierFree

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Data.List (isInfixOf)

import Logic.Export.Utils

import Logic.Formulas

binOpToSMTLib :: BinOp -> String
binOpToSMTLib Conj = "and"
binOpToSMTLib Disj = "or"
binOpToSMTLib Impl = "=>"
binOpToSMTLib Equiv = "="


varToSMTLib :: (MonadExport m) => Var -> m String
varToSMTLib (In x)      = return ("in-" ++ x)
varToSMTLib (Out x)     = return ("out-" ++ x)
varToSMTLib (Local i _) = getVarName i

tagToSMTLib ::  String -> String
tagToSMTLib x = "T" ++ x

letterToSMTLib :: Char -> String
letterToSMTLib x = "L" ++ safeEncodeLetter x

boolSetSMTLib :: String
boolSetSMTLib = "Bool"

posSetSMTLib :: String
posSetSMTLib = "Int"

alphSetSMTLib :: String
alphSetSMTLib = "Alph"

tagSetSMTLib :: String
tagSetSMTLib = "Tags"

sortToSMTLib :: Sort -> String
sortToSMTLib Boolean = boolSetSMTLib
sortToSMTLib Pos = posSetSMTLib
sortToSMTLib Tag = tagSetSMTLib

testOpToSMTLib :: TestOp -> String
testOpToSMTLib Eq  = "="
testOpToSMTLib Neq = "distinct"
testOpToSMTLib Lt  = "<"
testOpToSMTLib Le  = "<="
testOpToSMTLib Gt  = ">"
testOpToSMTLib Ge  = ">="
    


formulaToSMTLib :: (MonadExport m) => Formula String -> m String
formulaToSMTLib (FConst True) = return "true"
formulaToSMTLib (FConst False) = return "false"
formulaToSMTLib (FVar x) = varToSMTLib x
formulaToSMTLib (FBin op left right) = do
    l <- formulaToSMTLib left
    r <- formulaToSMTLib right
    let op' = binOpToSMTLib op
    return $ "(" ++ op' ++ " " ++ l ++ " " ++ r ++ ")"
formulaToSMTLib (FNot inner) = do
    i <- formulaToSMTLib inner
    return $ "(not " ++ i ++ ")"
formulaToSMTLib (FTestPos op x y) = do 
    vx <- varToSMTLib x
    vy <- varToSMTLib y
    let op' = testOpToSMTLib op
    return $ "(" ++ op' ++ " "  ++ vx ++  " " ++ vy ++ ")"
formulaToSMTLib (FTag x tag) = do
    vx <- varToSMTLib x
    let tx = tagToSMTLib tag
    return $ "(= " ++ vx ++ " " ++ tx ++ ")"
formulaToSMTLib (FLetter x letter) = do
    vx <- varToSMTLib x
    let lx = letterToSMTLib letter
    return $ "(= (word " ++ vx ++ ") " ++ lx ++ ")"
formulaToSMTLib (FRealPos x) = do
    vx <- varToSMTLib x
    -- return $ "(distinct Blank (word " ++ vx ++ "))"
    return $ "(and (>= " ++ vx ++ " 0) (< " ++ vx ++ " size) (distinct Blank (word " ++ vx ++ ")))"
formulaToSMTLib (FQuant Exists _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToSMTLib inner
        return $ "(exists ((" ++ n ++ " " ++ sortToSMTLib s ++ ")) " ++ i ++ ")"
formulaToSMTLib (FQuant Forall _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToSMTLib inner
        return $ "(forall ((" ++ n ++ " " ++ sortToSMTLib s ++ ")) " ++ i ++ ")"
 
-- (declare-datatype Name ((Constr1) (Constr2) ...))
declateDatatype :: String -> [String] -> String
declateDatatype name constructors = "(declare-datatype " ++ name ++ " (" ++ unwords cstrs ++ "))"
    where
        cstrs = intersperse " " $ map (\x -> "(" ++ x ++ ")") constructors


encodeSMTLib :: EncodeParams -> Formula String -> String
encodeSMTLib (EncodeParams alphabet tags) formula = unlines $ [preamble,
                                                               alphabetVarsDef, 
                                                               tagsVarsDef,
                                                               wordFunc,
                                                               wordSize,
                                                               wordSizeNonNeg,
                                                               blankDesc,
                                                               formula',
                                                               checkSat]
    where
        -- layout 
        --
        -- alphabet : Sort = list of all characters + Blank
        -- tags : Sort = list of all tags
        --
        -- word : Int -> Alphabet
        -- size : Int (size of the word, possibly zero)
        --
        -- 1) word i = Blank <=> i < 0 or i >= size
        -- 2) size >= 0
        -- 
        -- and this is it.
        --
        preamble = "(set-logic UFDTLIA)"

        alphabetVars :: [String]
        alphabetVars = "Blank" : map letterToSMTLib alphabet

        tagsVars     :: [String]
        tagsVars     = map tagToSMTLib tags

        alphabetVarsDef = declateDatatype alphSetSMTLib alphabetVars
        tagsVarsDef     = declateDatatype tagSetSMTLib tagsVars

        wordSize :: String
        wordSize = "(declare-const size Int)"

        wordFunc :: String
        wordFunc = "(declare-fun word (Int) " ++ alphSetSMTLib ++ ")"

        wordSizeNonNeg = "(assert (>= size 0))"
        blankDesc      = "(assert (forall ((i Int)) (= (or (< i 0) (>= i size)) (= (word i) Blank))))"

        formula' = "(assert " ++ (runExportM $ formulaToSMTLib formula) ++ ")"

        checkSat = "(check-sat)"




data SMTLibSolver = CVC5 | Z3 | Yices | AltErgo deriving (Show, Eq)

callSMTSolver :: SMTLibSolver -> String -> IO (ExitCode, String, String)
callSMTSolver CVC5 file    = readProcessWithExitCode "cvc5" [
                                    "--lang=smt2", file,
                                    "--tlimit=30000",
                                    "--cut-all-bounded",
                                    "--dt-blast-splits",
                                    "--dt-infer-as-lemmas",
                                    "--cbqi",
                                    "--cegqi",
                                    "--cegqi-nested-qe"
                                ] ""
callSMTSolver Z3 file      = readProcessWithExitCode "z3" ["-smt2", file] ""
callSMTSolver Yices file   = readProcessWithExitCode "yices-smt2" [file] ""
callSMTSolver AltErgo file = readProcessWithExitCode "alt-ergo" [
                                    "--input=smtlib2", file,
                                    "--instantiation-heuristic=greedy",
                                    "--no-nla",
                                    "--timelimit=30"
                                ] ""

outputToSMTLibResult :: SMTLibSolver -> String -> ExportResult
outputToSMTLibResult _ output = if isUnsat then Unsat else if isSat then Sat else Unknown
    where
        containsUnsat = "unsat"   `isInfixOf` output
        containsUnk   = "unknown" `isInfixOf` output
        containsSat   = "sat"     `isInfixOf` output

        isUnsat = containsUnsat && (not containsUnk)
        isUnk   = (not containsUnsat) && (not containsSat) && containsUnk
        isSat   = (not containsUnsat) && (not containsUnk) && containsSat


runSMTLib :: SMTLibSolver -> String -> IO ExportResult
runSMTLib solver input = do
    writeFile "tmp.smtlib" input
    (exitCode, output, _) <- callSMTSolver solver "tmp.smtlib"
    if exitCode /= ExitSuccess then 
        return Unknown
    else
        return $ outputToSMTLibResult solver output

