{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Mona where

import QuantifierFree

import Control.Monad
import Control.Monad.State

import Data.Char

import Data.Map (Map)
import qualified Data.Map as M

import System.IO.Temp (withSystemTempFile)
import System.Process (readProcess)
import Data.List (isInfixOf)

import GHC.IO.Handle (hPutStr)

import Logic.Formulas

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (x:xs) = x : sep : intersperse sep xs

-- we convert the debrujin indices into strings
-- for the mona export. This means we need a way
-- to create fresh names for variables, and also
-- to get the name of a variable "at quantifier depth i".

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


binOpToMona :: BinOp -> String
binOpToMona Conj = "&"
binOpToMona Disj = "|"
binOpToMona Impl = "=>"
binOpToMona Equiv = "<=>"

testOpToMona :: TestOp -> String
testOpToMona Eq = "="
testOpToMona Neq = "!="
testOpToMona Lt = "<"
testOpToMona Le = "<="
testOpToMona Gt = ">"
testOpToMona Ge = ">="
    

varToMona :: (MonadExport m) => Var -> m String
varToMona (In x) = return ("in_" ++ x)
varToMona (Out x) = return ("out_" ++ x)
varToMona (Local i _) = getVarName i

tagToMona ::  String -> String
tagToMona x = "T" ++ x

letterToMona :: Char -> String
letterToMona x = if Data.Char.isAlpha x then 
                    "L" ++ [x]
                 else 
                    "L" ++ show (Data.Char.ord x)

boolSetMona :: String
boolSetMona = "B"

posSetMona :: String
posSetMona = "P"

tagSetMona :: String
tagSetMona = "T"

realPosSetMona :: String
realPosSetMona = "W"


sortToMona :: Sort -> String
sortToMona Boolean = boolSetMona
sortToMona Pos = posSetMona
sortToMona Tag = tagSetMona


formulaToMona :: (MonadExport m) => Formula String -> m String
formulaToMona (FConst True) = return "true"
formulaToMona (FConst False) = return "false"
formulaToMona (FVar x) = do
    name <- varToMona x
    return $ "(" ++ name ++ " in BTrue)"
formulaToMona (FBin op left right) = do
    l <- formulaToMona left
    r <- formulaToMona right
    let op' = binOpToMona op
    return $ "( " ++ l ++ " " ++ op' ++ " " ++ r ++ " )"
formulaToMona (FNot inner) = do
    i <- formulaToMona inner
    return $ "~( " ++ i ++ " )"
formulaToMona (FTestPos op x y) = do 
    vx <- varToMona x
    vy <- varToMona y
    let op' = testOpToMona op
    return $ "( " ++ vx ++ " " ++ op' ++ " " ++ vy ++ " )"
formulaToMona (FTag x tag) = do
    vx <- varToMona x
    let tx = tagToMona tag
    return $ "( " ++ vx ++ " in " ++ tx ++ " )"
formulaToMona (FLetter x letter) = do
    vx <- varToMona x
    let lx = letterToMona letter
    return $ "( " ++ vx ++ " in " ++ lx ++ " )"
formulaToMona (FPredPos p x) = do
    px <- varToMona p
    vx <- varToMona x
    return $ "( " ++ px ++ " = " ++ vx ++ " - 1 )"
formulaToMona (FRealPos x) = do
    vx <- varToMona x
    return $ "( " ++ vx ++ " in " ++ realPosSetMona ++ " )"
formulaToMona (FQuant Exists _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "ex1 " ++ n ++ ": ( " ++ n ++ " in " ++ sortToMona s ++ " ) & ( " ++ i ++ " )"
formulaToMona (FQuant Forall _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "all1 " ++ n ++ ": ( " ++ n ++ " in " ++ sortToMona s ++ " ) => ( " ++ i ++ " )"
 
data EncodeParams = EncodeParams {
    alphabet :: String,
    tags     :: [String]
} deriving (Eq,Show)

encodeMona :: EncodeParams -> Formula String -> String
encodeMona (EncodeParams alphabet tags) formula = unlines $ [preamble, alphabetVarsDef, tagsVarsDef, layoutvarsDef, boolVarsDef, boolVarsPositions, tagVarsPositions, fakePosPosition, boolSortConstraint, tagSortConstraint, realPosConstraints, lettersAreDisjoint, layoutDisjoint, covering, formula']
    where
        -- layout 
        -- | tt | ff | t1 | t2 | ... | tn | ε | w1 | w2 | ... | wk |
        -- |---------|--------------------|---|--------------------|
        --  booleans     tags               0     input word
        --
        -- the "0" is to provide a valid position in the case of the
        -- empty word.
        preamble = "m2l-str;"

        layoutVars :: [String]
        layoutVars   = [realPosSetMona, boolSetMona, tagSetMona, posSetMona]

        alphabetVars :: [String]
        alphabetVars = map letterToMona alphabet

        tagsVars     :: [String]
        tagsVars     = map tagToMona tags

        boolVars     :: [String]
        boolVars     = ["BTrue", "BFalse"]
    
        alphabetVarsDef = "var2 " ++ unwords (intersperse "," alphabetVars) ++ ";"
        tagsVarsDef     = "var2 " ++ unwords (intersperse "," tagsVars) ++ ";"
        layoutvarsDef   = "var2 " ++ unwords (intersperse "," layoutVars) ++ ";"
        boolVarsDef     = "var2 " ++ unwords (intersperse "," boolVars) ++ ";"

        boolVarsPositions = unlines $ do
            (i, name) <- zip [0..] boolVars
            ["assert ( " ++ name ++ " = {" ++ show i ++ "});"]

        tagVarsPositions = unlines $ do 
            (i, name) <- zip [2..] tagsVars
            ["assert ( " ++ name ++ " = {" ++ show i ++ "});"]

        fakePositionNumber = length (boolVars) + length (tagsVars)

        fakePosPosition = "assert ( " ++ posSetMona ++ " = " ++ realPosSetMona ++ " union {" ++ show fakePositionNumber ++ "});"

        boolSortConstraint = "assert (" ++ boolSetMona ++ " = " ++ unwords (intersperse " union " boolVars) ++ ");"
        tagSortConstraint  = "assert (" ++ tagSetMona ++ " = " ++ unwords (intersperse " union " tagsVars) ++ ");"
        realPosConstraints  = "assert (" ++ realPosSetMona ++ " = " ++ unwords (intersperse " union " (alphabetVars)) ++ ");"
            
        lettersAreDisjoint :: String
        lettersAreDisjoint = unlines $ [
                "assert (" ++ (letterToMona a) ++ " inter " ++ (letterToMona b) ++ " = empty);" |
                a <- alphabet,
                b <- alphabet,
                a /= b
            ]

        layoutDisjoint :: String
        layoutDisjoint = unlines $ [
            "assert(" ++ boolSetMona ++ " inter " ++ tagSetMona ++ " = empty);",
            "assert(" ++ boolSetMona ++ " inter " ++ posSetMona ++ " = empty);",
            "assert(" ++ posSetMona  ++ " inter " ++ tagSetMona ++ " = empty);"
            ]
 
        covering = "assert (all1 x: (x in " ++ tagSetMona ++ ") | (x in " ++ boolSetMona ++ ") | (x in "++ posSetMona ++"));"
        formula' = (runExportM $ formulaToMona formula) ++ ";"


data MonaResult = Sat | Unsat | Unknown
  deriving (Show, Eq)



parseMonaOutput :: String -> MonaResult
parseMonaOutput output = if "Formula is valid" `isInfixOf` output then Sat else if "A satisfying example" `isInfixOf` output then Sat else if "Formula is unsatisfiable" `elem` lines output then Unsat else Unknown

runMona :: String -> IO MonaResult
runMona input = do
    -- write using the handle and not the file name
    writeFile "tmp.mona" input
    output <- readProcess "mona" ["-q", "tmp.mona"] ""
    return $ parseMonaOutput output
