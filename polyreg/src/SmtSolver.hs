module SmtSolver where

import TwoSortedFormulas (Formula(..), Quant(..), Sort(..))
import QuantifierFree

import Data.List (isInfixOf)

import System.Process

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (x:xs) = x : sep : intersperse sep xs

data SmtResult = Sat | Unsat | Unknown
  deriving (Show, Eq)


-- The encoding is as follows
-- we create a part of the word containing labels
-- and a part of the word containing positions of the input word
-- so the word in MONA is split in two: tags (T) and positions (W)

toMona :: Formula String Char -> String
toMona FTrue = "true"
toMona FFalse = "false"
toMona (FQuant Exists var Tag inner) = "ex1 " ++ var ++ ": ( " ++ var ++ " in T ) & ( " ++ toMona inner ++ " )"
toMona (FQuant Forall var Tag inner) = "all1 " ++ var ++ ": ( " ++ var ++ " in T ) => ( " ++ toMona inner ++ " )"
toMona (FQuant Exists var Pos inner) = "ex1 " ++ var ++ ": ( " ++ var ++ " in W ) & ( " ++ toMona inner ++ " )"
toMona (FQuant Forall var Pos inner) = "all1 " ++ var ++ ": ( " ++ var ++ " in W ) => ( " ++ toMona inner ++ " )"
toMona (FBin Conj left right) = "( " ++ toMona left ++ " & " ++ toMona right ++ " )"
toMona (FBin Disj left right) = "( " ++ toMona left ++ " | " ++ toMona right ++ " )"
toMona (FBin Impl left right) = "( " ++ toMona left ++ " => " ++ toMona right ++ " )"
toMona (FBin Equiv left right) = "( " ++ toMona left ++ " <=> " ++ toMona right ++ " )"
toMona (FNot inner) = "~( " ++ toMona inner ++ " )"
toMona (FTestPos Eq x y)  = "(" ++ x ++ " = " ++ y ++ ")"
toMona (FTestPos Neq x y) = "(" ++ x ++ " != " ++ y ++ ")"
toMona (FTestPos Lt x y)  = "(" ++ x ++ " < " ++ y ++ ")"
toMona (FTestPos Le x y)  = "(" ++ x ++ " <= " ++ y ++ ")"
toMona (FTestPos Gt x y)  = "(" ++ x ++ " > " ++ y ++ ")"
toMona (FTestPos Ge x y)  = "(" ++ x ++ " >= " ++ y ++ ")"
toMona (FTag x tag) = "(" ++ x ++ " in T" ++ tag ++ ")"
toMona (FLetter x letter) = "(" ++ x ++ " in L" ++ [letter] ++ ")"

encodeMona :: String -> [String] -> Formula String Char -> String
encodeMona alphabet tags formula = unlines $ [preamble, alphabetVarsDef, tagsVarsDef, wordVars, labelsAt, labelsUnion, wordUnion, disjoint, wordDisjoint, covering, formula']
    where
        preamble = "m2l-str;"
        alphabetVars = ["L" ++ [name] | name <- alphabet]
        tagsVars     = ["T" ++ name | name <- tags]
        wordVars = "var2 W,T;"

        alphabetVarsDef = "var2 " ++ unwords (intersperse "," alphabetVars) ++ ";"
        tagsVarsDef = "var2 " ++ unwords (intersperse "," tagsVars) ++ ";"

        labelAtI :: Int -> String -> String
        labelAtI i name = "assert (" ++ name ++ " = {" ++ show i ++ "});"

        labelsAt :: String
        labelsAt = concat . intersperse "\n" $ [labelAtI i name | (i, name) <- zip [0..] tagsVars ]

        labelsUnion = "assert (T = " ++ unwords (intersperse " union " tagsVars) ++ ");"
        wordUnion = "assert (W = " ++ unwords (intersperse " union " alphabetVars) ++ ");"
        wordDisjoint = unlines [ "assert (L" ++ [a] ++ " inter L" ++ [b] ++ " = empty);" | a <- alphabet, b <- alphabet, a /= b ]
        disjoint = "assert (T inter W = empty);"

        covering = "assert (all1 x: (x in T) | (x in W));"

        formula' = toMona formula ++ ";"

parseMonaOutput :: String -> SmtResult
parseMonaOutput output = if "Formula is valid" `isInfixOf` output then Sat else if "A satisfying example" `isInfixOf` output then Sat else if "Formula is unsatisfiable" `elem` lines output then Unsat else Unknown

-- use TmpDir to store the file
runMona :: String -> IO SmtResult
runMona input = do
    writeFile "tmp.mona" input
    output <- readProcess "mona" ["-q", "tmp.mona"] ""
    return $ parseMonaOutput output
