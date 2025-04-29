{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Export.Mona where


import System.Timeout

import Logic.QuantifierFree

import Data.List (isInfixOf)

import Logic.Formulas

import Logic.Export.Utils


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
letterToMona x = "L" ++ safeEncodeLetter x

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
formulaToMona (FBin Impl left right) = formulaToMona (FBin Disj (FNot left) right)
formulaToMona (FBin op left right) = do
    l <- formulaToMona left
    r <- formulaToMona right
    let op' = binOpToMona op
    return $ "( " ++ l ++ " " ++ op' ++ " " ++ r ++ " )"
formulaToMona (FNot inner) = do
    i <- formulaToMona inner
    return $ "(~( " ++ i ++ " ))"
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
formulaToMona (FRealPos x) = do
    vx <- varToMona x
    return $ "( " ++ vx ++ " in " ++ realPosSetMona ++ " )"
formulaToMona (FQuant Exists _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "(ex1 " ++ n ++ ": (( " ++ n ++ " in " ++ sortToMona s ++ " ) & ( " ++ i ++ " )))"
formulaToMona (FQuant Forall _ s inner) = do
    withVariable s $ do
        n <- getVarName 0
        i <- formulaToMona inner
        return $ "(all1 " ++ n ++ ": ((~ ( " ++ n ++ " in " ++ sortToMona s ++ " )) | ( " ++ i ++ " )))"
 

encodeMona :: EncodeParams -> Formula String -> String
encodeMona (EncodeParams alphabet tags) formula = unlines $ [preamble, alphabetVarsDef, tagsVarsDef, layoutvarsDef, boolVarsDef, boolVarsPositions, tagVarsPositions, fakePosPosition, fakePosIsNotReal, boolSortConstraint, tagSortConstraint, realPosConstraints, lettersAreDisjoint, layoutDisjoint, covering, formula']
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
        realPosConstraints = "assert (" ++ realPosSetMona ++ " = " ++ unwords (intersperse " union " (alphabetVars)) ++ ");"
        fakePosIsNotReal   = "assert (~(" ++ show fakePositionNumber ++ " in " ++ realPosSetMona ++ "));"
            
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



parseMonaOutput :: String -> ExportResult
parseMonaOutput output = if "Formula is valid" `isInfixOf` output then Sat else if "A satisfying example" `isInfixOf` output then Sat else if "Formula is unsatisfiable" `elem` lines output then Unsat else Unknown

timeLimit :: Int 
timeLimit = 30


runMona :: String -> IO ExportResult
runMona input = withTempFileContent input $ \ifile -> do
        outputCmd <- timeout (10^6 * timeLimit)  $ safeRunProcess "mona" ["-o2", "-q", ifile]
        case outputCmd of
            Just (Left err) -> do
                -- putStrLn $ "File: " ++ ifile
                -- putStrLn input
                -- putStrLn $ "Error: " ++ err
                return $ Error err
            Just (Right output) -> return $ parseMonaOutput output
            Nothing             -> return $ Unknown
