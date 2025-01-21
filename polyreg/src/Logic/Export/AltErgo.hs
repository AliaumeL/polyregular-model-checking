{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Export.AltErgo where

import QuantifierFree

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Data.List (isInfixOf)

import Logic.Formulas

import Logic.Export.Utils

encodeBinOp :: BinOp -> String
encodeBinOp Conj  = "and"
encodeBinOp Disj  = "or"
encodeBinOp Impl  = "->"
encodeBinOp Equiv = "<->"

encodeVar :: Var -> ExportM String
encodeVar (In x)      = return $ "in_" ++ x
encodeVar (Out x)     = return $ "out_" ++ x
encodeVar (Local i _) = getVarName i

encodeTag ::  String -> String
encodeTag x = "T" ++ x

encodeLetter :: Char -> String
encodeLetter x = "L" ++ safeEncodeLetter x

encodeBoolSet :: String
encodeBoolSet = "bool"

encodePosSet :: String
encodePosSet = "int"

encodeLetterSet :: String
encodeLetterSet = "alphabet"

encodeTagSet :: String
encodeTagSet = "tags"

encodeSort :: Sort -> String
encodeSort Boolean = encodeBoolSet
encodeSort Pos     = encodePosSet
encodeSort Tag     = encodeTagSet

encodeTestOp :: TestOp -> String
encodeTestOp Eq  = "="
encodeTestOp Neq = "<>"
encodeTestOp Lt  = "<"
encodeTestOp Le  = "<="
encodeTestOp Gt  = ">"
encodeTestOp Ge  = ">="

encodeFormula :: Formula String -> ExportM String
encodeFormula (FConst True ) = return "true"
encodeFormula (FConst False) = return "false"
encodeFormula (FVar x) = encodeVar x
encodeFormula (FBin op left right) = do
    l <- encodeFormula left
    r <- encodeFormula right
    let op' = encodeBinOp op
    return $ "(" ++ l ++ " " ++ op' ++ " " ++ r ++ ")"
encodeFormula (FNot inner) = do
    i <- encodeFormula inner
    return $ "not (" ++ i ++ ")"
encodeFormula (FTestPos op x y) = do
    vx <- encodeVar x
    vy <- encodeVar y
    let op' = encodeTestOp op
    return $ "(" ++ vx ++ " " ++ op' ++ " " ++ vy ++ ")"
encodeFormula (FTag x tag) = do
    vx <- encodeVar x
    let tx = encodeTag tag
    return $ "(" ++ tx ++ " = " ++ vx ++ ")"
encodeFormula (FLetter x letter) = do
    vx <- encodeVar x
    let lx = encodeLetter letter
    return $ "( word(" ++ vx ++ ") = " ++ lx ++ ")"
encodeFormula (FRealPos x) = do
    vx <- encodeVar x
    return $ "((" ++ vx ++ " >=  0) and (" ++ vx ++ " < size))"
encodeFormula (FQuant Exists _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- encodeFormula inner
        return $ "(exists " ++ n ++ " : " ++ encodeSort s ++ ". " ++ i ++ ")"
encodeFormula (FQuant Forall _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- encodeFormula inner
        return $ "(forall " ++ n ++ " : " ++ encodeSort s ++ ". " ++ i ++ ")"


-- (declare-datatype Name ((Constr1) (Constr2) ...))
encodeDatatype :: String -> [String] -> String
encodeDatatype name constructors = "type " ++ name ++ " = " ++ unwords cstrs ++ "\n\n"
    where
        cstrs = intersperse " | " $ constructors

encodeAltErgo :: EncodeParams -> Formula String -> String
encodeAltErgo (EncodeParams alphabet tags) formula = unlines $ [
                                                                alphabetVarsDef, 
                                                                tagsVarsDef,
                                                                wordFunc,
                                                                wordSize,
                                                                wordSizeNonNeg,
                                                                blankDesc,
                                                                formula' ]
    where
        -- layout 
        --
        -- alphabet : Sort = list of all characters + Blank
        -- tags : Sort = list of all tags
        --
        -- logic word : Int -> Alphabet
        -- logic size : Int (size of the word, possibly zero)
        --
        -- 1) word i = Blank <=> i < 0 or i >= size
        -- 2) size >= 0
        -- 
        -- and this is it.
        --
        alphabetVars :: [String]
        alphabetVars = "Blank" : map encodeLetter alphabet

        tagsVars     :: [String]
        tagsVars     = map encodeTag tags

        alphabetVarsDef = encodeDatatype encodeLetterSet alphabetVars
        tagsVarsDef     = encodeDatatype encodeTagSet    tagsVars

        wordSize :: String
        wordSize = "logic size : int"

        wordFunc :: String
        wordFunc = "logic word : int -> " ++ encodeLetterSet

        wordSizeNonNeg = "axiom wordNonEmpty : size >= 0"
        blankDesc      = "axiom blanksOut    : forall i : int. ((i < 0) or (i >= size)) <-> ( word(i) = Blank)" 

        formula' = "goal altergoGoal: " ++ (runExportM $ encodeFormula formula)


altErgoCmd :: String -> (String, [String])
altErgoCmd file = ("alt-ergo", [
                                           "--timelimit=30",
                                           "--instantiation-heuristic=greedy",
                                           "--no-nla",
                                           file
                                           ])

outputToResult :: String -> ExportResult
outputToResult output = if isUnsat then Unsat else if isSat then Sat else Unknown
    where
        containsUnsat = "unsat"   `isInfixOf` output
        containsUnk   = "unknown" `isInfixOf` output
        containsSat   = "sat"     `isInfixOf` output

        isUnsat = containsUnsat && (not containsUnk)
        isUnk   = (not containsUnsat) && (not containsSat) && containsUnk
        isSat   = (not containsUnsat) && (not containsUnk) && containsSat


runAltErgo :: String -> IO ExportResult
runAltErgo input = do
    writeFile "tmp.ae" input
    let (cmd, args) = altErgoCmd "tmp.ae"
    outputCmd <- safeRunProcess cmd args
    case outputCmd of
        Left err     -> return $ Error err
        Right output -> return $ outputToResult output

