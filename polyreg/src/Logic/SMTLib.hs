{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.SMTLib where

import QuantifierFree

import Control.Monad
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as M

import System.IO.Temp (withSystemTempFile)
import System.Process (readProcess)
import Data.List (isInfixOf)

import Data.Char

import Logic.Formulas

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (x:xs) = x : sep : intersperse sep xs

class (Monad m) => MonadExport m where
    withVariable  :: Sort -> m a -> m a
    getVarName    :: Int -> m String

data ExportState = ExportState { varStack :: [String], nextVar :: Int } deriving(Eq, Show)

newtype ExportM a = ExportM (State ExportState a) 
    deriving(Monad,Applicative,Functor, MonadState ExportState)

instance MonadExport ExportM where
    withVariable s (ExportM m) = do
        count <- gets nextVar
        stack <- gets varStack
        let newVar = take 1 (show s) ++ show count
        modify (\(ExportState m n) -> ExportState (newVar : m) (n+1))
        res <- ExportM m
        modify (\(ExportState m n) -> ExportState stack n)
        return res
    getVarName i = do
        stack <- gets varStack
        return $ stack !! i

runExportM :: ExportM a -> a
runExportM (ExportM m) = evalState m (ExportState [] 0)


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
letterToSMTLib x = if Data.Char.isAlpha x then 
                      "L" ++ [x]
                   else 
                      "L" ++ show (Data.Char.ord x)

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
formulaToSMTLib (FPredPos p x) = do
    px <- varToSMTLib p
    vx <- varToSMTLib x
    return $ "(= " ++ px ++ " (- " ++ vx ++ " ))"
formulaToSMTLib (FRealPos x) = do
    vx <- varToSMTLib x
    return $ "(distinct Blank (word " ++ vx ++ "))"
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
 
data EncodeParams = EncodeParams {
    alphabet :: String,
    tags     :: [String]
} deriving (Eq,Show)


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
                                                               blankOutsideWord,
                                                               notBlankInsideWord,
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
        blankOutsideWord   = "(assert (forall ((i Int)) (=> (or (< i 0) (>= i size)) (= (word i) Blank))))"
        notBlankInsideWord = "(assert (forall ((i Int)) (=> (and (>= i 0) (< i size)) (distinct (word i) Blank))))"

        formula' = "(assert " ++ (runExportM $ formulaToSMTLib formula) ++ ")"

        checkSat = "(check-sat)"


data SMTLibResult = Sat | Unsat | Unknown
  deriving (Show, Eq)



parseSMTLibOutput :: String -> SMTLibResult
parseSMTLibOutput output = if "Formula is valid" `isInfixOf` output then Sat else if "A satisfying example" `isInfixOf` output then Sat else if "Formula is unsatisfiable" `elem` lines output then Unsat else Unknown


data SMTLibSolver = CVC5 | Z3 | Yices | AltErgo deriving (Show, Eq)

callSMTSolver :: SMTLibSolver -> String -> IO String
callSMTSolver CVC5 file = readProcess "cvc5" ["--lang=smt2", file] ""
callSMTSolver Z3 file = readProcess "z3" ["-smt2", file] ""
callSMTSolver Yices file = readProcess "yices-smt2" [file] ""
callSMTSolver AltErgo file = readProcess "alt-ergo" ["-i smtlib2", file] ""

outputToSMTLibResult :: SMTLibSolver -> String -> SMTLibResult
outputToSMTLibResult _ output = if isUnsat then Unsat else if isSat then Sat else Unknown
    where
        containsUnsat = "unsat"   `isInfixOf` output
        containsUnk   = "unknown" `isInfixOf` output
        containsSat   = "sat"     `isInfixOf` output

        isUnsat = containsUnsat && (not containsUnk)
        isUnk   = (not containsUnsat) && (not containsSat) && containsUnk
        isSat   = (not containsUnsat) && (not containsUnk) && containsSat


runSMTLib :: SMTLibSolver -> String -> IO SMTLibResult
runSMTLib solver input = do
    writeFile "tmp.smtlib" input
    output <- callSMTSolver solver "tmp.smtlib"
    return $ outputToSMTLibResult solver output

