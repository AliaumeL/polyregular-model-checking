{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MonaExport where

import QuantifierFree
import ThreeSortedFormulas

import Control.Monad
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as M

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
runExportM (ExportM m) = evalState m (ExportState M.empty 0 0)


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

tagToMona :: (MonadExport m) => String -> m String
tagToMona (Tag x) = return ("T" ++ lower x)

letterToMona :: (MonadExport m) => Char -> m String
letterToMona x = return ("L" ++ [x])

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
formulaToMona (FVar x) = return x
formulaToMona (FBin op left right) = do
    l <- formulaToMona left
    r <- formulaToMona right
    let op' = opToMona op
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
    tx <- tagToMona tag
    return $ "( " ++ vx ++ " in " ++ tx ++ " )"
formulaToMona (FLetter x letter) = do
    vx <- varToMona x
    lx <- letterToMona letter
    return $ "( " ++ vx ++ " in " ++ lx ++ " )"
formulaToMona (FPredPos p x) = do
    px <- varToMona p
    vx <- varToMona x
    return $ "( " ++ px ++ " = " ++ vx ++ " - 1 )"
formulaToMona (FRealPos x) = do
    vx <- varToMona x
    return $ "( " ++ vx ++ " in " ++ realPosSetMona ++ " )"
formulaToMona (FQuant Exists s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "ex1 " ++ n ++ ": ( " ++ n ++ " in " ++ sortToMona s ++ " ) & ( " ++ i ++ " )"
formulaToMona (FQuant Forall s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "all1 " ++ n ++ ": ( " ++ n ++ " in " ++ sortToMona s ++ " ) => ( " ++ i ++ " )"
 
data EncodeParams = EncodeParams {
    alphabet :: String,
    tags     :: [String]
} deriving (Eq,Show)

encodeMona :: EncodeParams -> Formula String -> String
encodeMona (EncodeParams alphabet tags) formula = unlines $ [preamble, alphabetVarsDef, tagsVarsDef, wordVars, labelsAt, labelsUnion, wordUnion, disjoint, wordDisjoint, covering, formula']
    where
        -- layout 
        -- | tt | ff | t1 | t2 | ... | tn | ε | w1 | w2 | ... | wk |
        -- |---------|--------------------|---|--------------------|
        --  booleans     tags               0     input word
        --
        -- the "0" is to provide a valid position in the case of the
        -- empty word.
        preamble = "m2l-str;"

        layoutVars   = [realPosSetMona, boolSetMona, tagSetMona, posSetMona]
        alphabetVars :: [String]
        alphabetVars = map letterToMona alphabet
        tagsVars     = map tagToMona tags
        boolVars     = ["BTrue", "BFalse"]
    
        alphabetVarsDef = "var2 " ++ unwords (intersperse "," alphabetVars) ++ ";"
        tagsVarsDef     = "var2 " ++ unwords (intersperse "," tagsVars) ++ ";"
        layoutvarsDef   = "var2 " ++ unwords (intersperse "," layoutVars) ++ ";"

        boolVarsPositions = unlines $ do
            (i, name) <- zip [0..] boolVars
            return $ "assert ( " ++ name ++ " = {" ++ show i ++ "});"

        tagVarsPositions = unlines $ do 
            (i, name) <- zip [2..] tagsVars
            return $ "assert ( " ++ name ++ " = {" ++ show i ++ "});"

        fakePositionNumber = length (boolVars) + length (tagsVars)

        fakePosPosition = "assert ( " ++ posSetMona ++ " = " ++ realPosSetMona ++ " union {" ++ show fakePositionNumber ++ "});"

        boolSortConstraint = "assert (" ++ boolSetMona ++ " = " ++ unwords (intersperse " union " boolVars) ++ ");"
        tagSortConstraint  = "assert (" ++ tagSetMona ++ " = " ++ unwords (intersperse " union " tagsVars) ++ ");"
        realPosConstraints  = "assert (" ++ realPosSetMona ++ " = " ++ unwords (intersperse " union " (alphabetVars)) ++ ");"
            
        lettersAreDisjoint :: [String]
        lettersAreDisjoint = unlines $ do
            a <- alphabet
            b <- alphabet
            if a == b then
                []
            else 
                return $ "assert (" ++ (letterToMona a) ++ " inter " ++ (letterToMona b) ++ " = empty);"

        layoutDisjoint = unlines $ [
            "assert(" ++ boolSetMona ++ " inter " ++ tagSetMona ++ " = empty);",
            "assert(" ++ boolSetMona ++ " inter " ++ posSetMona ++ " = empty);",
            "assert(" ++ posSetMona  ++ " inter " ++ tagSetMona ++ " = empty);"
            ]
 
        covering = "assert (all1 x: (x in " ++ tagSetMona ++ ") | (x in " ++ boolSetMona ++ ") | (x in "++ posSetMona ++"));"
        formula' = runExportM $ formulaToMona formula
