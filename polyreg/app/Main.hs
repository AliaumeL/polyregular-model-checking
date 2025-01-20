module Main (main) where


import ForPrograms
import ForProgramsTyping (ValueType(..))
import Typing.Inference (inferAndCheckProgram)
import ForProgramInterpreter (runProgramString, InterpretError(..))
import BooleanElimination (removeBooleanGen)
import FunctionElimination (eliminateFunctionCalls)
import LiteralElimination (eliminateLiterals)
import LetElimination (eliminateLetProgram)
import ForLoopExpansion (forLoopExpansion, forLoopExpansionFix)
import ReturnElimination (retElimProgram)
import ReductionLitEq (removeBLitEq)
import ForProgramsPrettyPrint
import Parser.ParseHighLevel (parseHighLevel)
import Typing.TypeChecker (typeCheckProgram)
import FinalConditions (finalConditions, displayBrokenConditions)
import ToSimpleForProgram (toSimpleForProgram)
import SimpleForPrograms (runProgram, pathToTag)
import qualified SimpleForPrograms as SFP
import LetBoolsToTop (bringLetBoolsToTopAndRefresh)
import SimpleForProgramSimplification (simplifyForProgram)
import QuantifierFree
import Logic.Formulas 
import Logic.PullBack (pullBack)
import Logic.Mona (encodeMona, runMona, EncodeParams(..), MonaResult(..))
import Logic.SMTLib (encodeSMTLib, runSMTLib, SMTLibResult(..), EncodeParams(..), SMTLibSolver(..))
import Logic.Interpreter (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))

import Data.List (nub)
import Debug.Trace (traceM)

import Options.Applicative


-- use optparse-applicative for the command line arguments
-- use the following options:
-- -i --input: the input file
-- -t --transformation: the transformations to apply (multiple calls means multiple transformations)
--      (by default all the transformations are selected)
--      - boolean-elimination  (b)
--      - function-elimination (f)
--      - literal-elimination  (l)
--      - reduction-lit-eq     (r)
--      - for-loop-expansion   (e)
-- -o --output: the output file (by default stdout)
-- -h --help: the help message
-- -v --version: the version of the program
-- -l --list: list all the transformations
-- -f --no-simplify : don't optimize the resulting simple for program 


data Transformation = LitEqElimination
                    | FunctionElimination
                    | LiteralElimination    -- litteral to generators
                    | BooleanElimination
                    | LetOutputElimination
                    | ReturnElimination
                    | ForLoopExpansion
                    | LetBoolsToTop
                    deriving (Eq,Show,Read,Ord,Enum)

transformationsInOrder :: [Transformation]
transformationsInOrder = [LitEqElimination .. LetBoolsToTop]


applyTransform :: Transformation -> Program String ValueType -> Program String ValueType
applyTransform BooleanElimination p = removeBooleanGen p
applyTransform FunctionElimination p = eliminateFunctionCalls p
applyTransform LiteralElimination p = eliminateLiterals p
applyTransform LitEqElimination p = removeBLitEq p
applyTransform LetOutputElimination p = eliminateLetProgram p
applyTransform ReturnElimination p = retElimProgram p
applyTransform ForLoopExpansion p = case forLoopExpansionFix p of  
    Left err -> error $ "Error in for loop expansion: " ++ show err
    Right p' -> p'
applyTransform LetBoolsToTop p = bringLetBoolsToTopAndRefresh p


data Options = Options
    { optInputProg :: Maybe FilePath
    , optInputWord :: Maybe String
    , optTransformations :: Maybe Int
    , optOutputProg :: Maybe FilePath
    , optOutputWord :: Maybe String
    , optNoSimplify :: Bool
    , optList :: Bool
    } deriving (Eq,Show)

options :: Parser Options
options = Options
    <$> optional (strOption (long "input-prog" <> short 'i' <> metavar "FILE" <> help "The input file"))
    <*> optional (strOption (long "input-word" <> short 'w' <> metavar "WORD" <> help "The input word"))
    <*> optional (option auto (long "transformation" <> short 't' <> metavar "TRANSFORMATION" <> help "The transformation to apply"))
    <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "The output file"))
    <*> optional (strOption (long "output-word" <> short 'W' <> metavar "WORD" <> help "The output word"))
    <*> switch (long "no-simplify" <> short 'f' <> help "Do not simplify the resulting simple for program")
    <*> switch (long "list" <> short 'l' <> help "List all the transformations")



cmdParser :: ParserInfo Options
cmdParser = info (options <**> helper)
    ( fullDesc
    <> progDesc "Transform a program"
    <> header "ForPrograms - a program transformation tool" )

readInputFile :: Maybe FilePath -> IO String
readInputFile Nothing = getContents
readInputFile (Just file) = readFile file

writeOutputFile :: Maybe FilePath -> String -> IO ()
writeOutputFile Nothing = putStrLn
writeOutputFile (Just file) = writeFile file

erasePositionTypes ::ValueType -> Maybe ValueType
erasePositionTypes (TPos _) = Nothing
erasePositionTypes t = Just t

eraseTypesInFunctions :: Program String ValueType -> Program String (Maybe ValueType)
eraseTypesInFunctions (Program fs main) = Program (map eraseTypesInFunctionsFun fs) main

eraseTypesInFunctionsFun :: StmtFun String ValueType -> StmtFun String (Maybe ValueType)
eraseTypesInFunctionsFun (StmtFun name args s t) = StmtFun name args' (fmap (const Nothing) s) (Just t)
    where args' = map (\(a, b, c) -> (a, Just b, c)) args

simpleShowInterpreterError :: InterpretError -> String
simpleShowInterpreterError (InterpretError s _) = s

simpleShowEitherError :: Either InterpretError String -> String
simpleShowEitherError (Left e) = "ERROR: " ++ simpleShowInterpreterError e
simpleShowEitherError (Right s) = "OK: " ++ s

encodeHoareTriple :: Formula () -> Interpretation String -> Formula () -> Formula String
encodeHoareTriple input i output = FBin Impl (injectTags input) (pullBack i output)

containsAB :: Formula ()
containsAB = quantifyList [("firstA", Pos, Exists), ("nextB", Pos, Exists)] $ andList [iLessThanJ, consecutive, iIsA, jIsB]
    where
        iLessThanJ = FTestPos Lt (Local 1 "firstA") (Local 0 "nextB")
        consecutive = FNot . quantifyList [("middleLetter", Pos, Exists)] . andList $ [
            FTestPos Lt (Local 2 "firstA") (Local 0 "middleLetter"),
            FTestPos Lt (Local 0 "middleLetter") (Local 1 "nextB") ]
        iIsA       = FLetter (Local 1 "firstA") 'a'
        jIsB       = FLetter (Local 0 "nextB")  'b'

startsWithA :: Formula ()
startsWithA = quantifyList [("firstA", Pos, Exists)] $ andList [iIsA, isFirst]
    where
        iIsA       = FLetter (Local 0 "firstA") 'a'
        isFirst    = FNot $ quantifyList [("beforeFirst", Pos, Exists)] $ FTestPos Lt (Local 0 "beforeFirst") (Local 1 "firstA")

endsWithB :: Formula ()
endsWithB = quantifyList [("lastB", Pos, Exists)] $ andList [jIsB, isLast]
    where
        jIsB       = FLetter (Local 0 "lastB") 'b'
        isLast     = FNot $ quantifyList [("afterLast", Pos, Exists)] $ FTestPos Lt (Local 1 "lastB") (Local 0 "afterLast")

containsAA :: Formula ()
containsAA = quantifyList [("firstA", Pos, Exists), ("nextB", Pos, Exists)] $ andList [iLessThanJ, consecutive, iIsA, jIsA]
    where
        iLessThanJ = FTestPos Lt (Local 1 "firstA") (Local 0 "nextB")
        consecutive = FNot . quantifyList [("middleLetter", Pos, Exists)] . andList $ [
            FTestPos Lt (Local 2 "firstA") (Local 0 "middleLetter"),
            FTestPos Lt (Local 0 "middleLetter") (Local 1 "nextB") ]
        iIsA       = FLetter (Local 1 "firstA") 'a'
        jIsA       = FLetter (Local 0 "nextB")  'a'


monaVerifyHoareTriple :: Formula () -> Interpretation String -> Formula () -> IO MonaResult
monaVerifyHoareTriple input i output = runMona encoded
    where
        triple  = simplifyFormula $ FNot (encodeHoareTriple input i output)
        params  = Logic.Mona.EncodeParams (nub $ "abcd" ++ Logic.Interpretation.alphabet i) (Logic.Interpretation.tags i)
        encoded = encodeMona params triple

smtLibVerifyHoareTriple :: SMTLibSolver -> Formula () -> Interpretation String -> Formula () -> IO SMTLibResult
smtLibVerifyHoareTriple solver input i output = runSMTLib solver encoded
    where
        triple  = simplifyFormula $ FNot (encodeHoareTriple input i output)
        params  = Logic.SMTLib.EncodeParams (nub $ "abcd" ++ Logic.Interpretation.alphabet i) (Logic.Interpretation.tags i)
        encoded = encodeSMTLib params triple


higherToSimpleProgram :: Program String ValueType -> SFP.ForProgram
higherToSimpleProgram p = simplifyForProgram sfp
    where
        transformedProg = foldl (flip applyTransform) p transformationsInOrder
        Right sfp = toSimpleForProgram transformedProg

simpleForToInterpretation :: SFP.ForProgram -> Interpretation String
simpleForToInterpretation sfp = Interpretation tags alphabet simplifiedDomain simplifiedOrder labelOrCopy arity
    where
        Interpretation tags alphabet domain order labelOrCopy arity = stringify pathToTag $  toInterpretation sfp
        simplifiedDomain = \s vs -> id $ domain s vs
        simplifiedOrder  = \s1 s2 vs1 vs2 -> simplifyFormula $ order s1 s2 vs1 vs2


main :: IO ()
main = do 
    opts <- execParser cmdParser
    progString <- readInputFile (optInputProg opts)
    putStrLn $ "Program: read"
    let (Right parsedProg)      = parseHighLevel progString
    putStrLn $ "Program: parsed"
    let (Right typedProg)       = inferAndCheckProgram parsedProg
    putStrLn $ "Program: typed"
    let simpleForProg           = higherToSimpleProgram typedProg
    putStrLn $ "Program: converted to simple for\n" ++ show simpleForProg
    let simpleForInterpretation = simpleForToInterpretation simpleForProg
    putStrLn $ "Program: converted to interpretation" ++ show simpleForInterpretation
    verifyResult <- monaVerifyHoareTriple containsAA simpleForInterpretation (FNot containsAA)
    -- (andList [startsWithA, endsWithB]) simpleForInterpretation containsAB
    putStrLn $ "Program: transformed to hoare triple (MONA)"
    case verifyResult of
        Logic.Mona.Unsat     -> putStrLn "[MONA] YES! The Hoare triple is       valid"
        Logic.Mona.Sat       -> putStrLn "[MONA] NO ! The Hoare triple is *not* valid"
        Logic.Mona.Unknown   -> putStrLn "[MONA] ???"
    verifyResult <- smtLibVerifyHoareTriple CVC5 containsAA simpleForInterpretation (FNot containsAA)
    -- (andList [startsWithA, endsWithB]) simpleForInterpretation containsAB
    putStrLn $ "Program: transformed to hoare triple (SMTLib)"
    case verifyResult of
        Logic.SMTLib.Unsat   -> putStrLn "[SMTLib] YES! The Hoare triple is       valid"
        Logic.SMTLib.Sat     -> putStrLn "[SMTLib] NO ! The Hoare triple is *not* valid"
        Logic.SMTLib.Unknown -> putStrLn "[SMTLib] ???"
    


{- 
main :: IO ()
main = do
    opts <- execParser cmdParser
    progString <- readInputFile (optInputProg opts)
    let word = optInputWord opts
    let parsedProgOrErr  = parseHighLevel progString 
    case parsedProgOrErr of
        Left err -> putStrLn . show $ err
        Right parsedProg -> do 
            let typedProg = inferAndCheckProgram parsedProg
            case typedProg of
                Left err -> putStrLn . show $ err
                Right prog -> do
                    let transformationSize = case optTransformations opts of
                                                Nothing -> length transformationsInOrder
                                                Just n -> n
                    let transformations = take transformationSize transformationsInOrder
                    putStrLn $ "Applying transformations: " ++ show transformations
                    let transformedProg = foldl (flip applyTransform) prog transformations
                    writeOutputFile (optOutputProg opts) (prettyPrintProgramWithNls prog)
                    writeOutputFile (optOutputProg opts) (replicate 80 '-')
                    writeOutputFile (optOutputProg opts) (prettyPrintProgramWithNls transformedProg)
                    case typeCheckProgram transformedProg of
                        Left err -> do 
                            putStrLn $ "Program stopped typechecking:\n " ++ err
                            let transformedProg' = eraseTypesInFunctions transformedProg
                            case inferAndCheckProgram transformedProg' of
                                Left err' -> putStrLn $ "Program still does not type check: " ++ show err'
                                Right _ -> putStrLn $ "Program could be type checked after erasing types"
                        Right _  -> putStrLn $ "Program still type checks"
                    case finalConditions transformedProg of
                        False -> putStrLn $ "The following conditions are broken:\n" ++ displayBrokenConditions transformedProg
                        True -> putStrLn $ "Final conditions are satisfied"
                    case word of
                        Nothing -> return ()
                        Just w -> do
                            let wordBefore = runProgramString (fmap (const ()) prog) w
                            let wordAfter  = runProgramString (fmap (const ()) transformedProg) w
                            writeOutputFile (optOutputWord opts) (replicate 80 '-')
                            writeOutputFile (optOutputWord opts) w
                            writeOutputFile (optOutputWord opts) (show wordBefore)
                            writeOutputFile (optOutputWord opts) (simpleShowEitherError wordAfter)
                            writeOutputFile (optOutputWord opts) ("Is the same: " ++ (show $ wordBefore == wordAfter))
                    let simpleForProg = toSimpleForProgram transformedProg
                    case simpleForProg of
                        Left err  -> putStrLn $ "Error in converting to simple for program: " ++ show err
                        Right sfp' ->
                            let sfp = if optNoSimplify opts then sfp' else simplifyForProgram sfp' in
                            case word of 
                            Nothing -> putStrLn "Converted to a simple for program, but nothing to be run on it"
                            Just w -> do
                                writeOutputFile (optOutputWord opts) (replicate 80 '-')
                                writeOutputFile (optOutputWord opts) (SFP.prettyPrintForProgram sfp)
                                -- traceM $ show $ optNoSimplify opts
                                --traceM $ SFP.prettyPrintForProgram sfp
                                let result = runProgram sfp w
                                writeOutputFile (optOutputWord opts) (replicate 80 '-')
                                writeOutputFile (optOutputWord opts) w
                                writeOutputFile (optOutputWord opts) (show result)
                                writeOutputFile (optOutputWord opts) (replicate 80 '-')
                                let result' = runAsInterpretation sfp w
                                writeOutputFile (optOutputWord opts) (show . sfpToInterpretation $ sfp)
                                writeOutputFile (optOutputWord opts) (show result')
                                return ()
-}
