module Main (main) where


import ForPrograms.HighLevel
import ForPrograms.HighLevel.Typing(ValueType(..))
import ForPrograms.HighLevel.Typing.Inference (inferAndCheckProgram)
import ForPrograms.HighLevel.Interpreter (runProgramString, InterpretError(..))
import ForPrograms.HighLevel.Transformations.BooleanElimination (removeBooleanGen)
import ForPrograms.HighLevel.Transformations.FunctionElimination (eliminateFunctionCalls)
import ForPrograms.HighLevel.Transformations.LiteralElimination (eliminateLiterals)
import ForPrograms.HighLevel.Transformations.LetElimination (eliminateLetProgram)
import ForPrograms.HighLevel.Transformations.ForLoopExpansion (forLoopExpansion, forLoopExpansionFix)
import ForPrograms.HighLevel.Transformations.ReturnElimination (retElimProgram)
import ForPrograms.HighLevel.Transformations.ReductionLitEq (removeBLitEq)
import ForPrograms.HighLevel.PrettyPrint
import Parser.ParseHighLevel (parseHighLevel)
import ForPrograms.HighLevel.Typing.TypeChecker (typeCheckProgram)
import ForPrograms.HighLevel.Transformations.FinalConditions (finalConditions, displayBrokenConditions)
import ForPrograms.HighLevel.ToSimple (toSimpleForProgram)
import ForPrograms.Simple (runProgram, pathToTag)
import qualified ForPrograms.Simple as SFP
import ForPrograms.HighLevel.Transformations.LetBoolsToTop (bringLetBoolsToTopAndRefresh)
import ForPrograms.Simple.Optimization(simplifyForProgram)
import Logic.QuantifierFree
import Logic.Formulas 
import Logic.HoareTriple    (HoareTriple(..), verifyHoareTriple, encodeHoareTriple)
import Logic.Export         (ExportResult(..), EncodeParams(..), allSolvers, installedSolvers)
import Logic.Interpreter    (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))

import Data.List (nub)
import Debug.Trace (traceM)

import Options.Applicative
import Control.Monad (forM_)


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
      <*> switch   (long "no-simplify" <> short 'f' <> help "Do not simplify the resulting simple for program")
      <*> switch   (long "list" <> short 'l' <> help "List all the transformations")



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


containsAB :: Char -> Char -> Formula ()
containsAB c1 c2 = quantifyList [("firstC", Pos, Exists), ("nextC", Pos, Exists)] $ andList [iLessThanJ, consecutive, iIsC, jIsC]
    where
        iLessThanJ = FTestPos Lt (Local 1 "firstC") (Local 0 "nextC")
        consecutive = FNot . quantifyList [("middleLetter", Pos, Exists)] . andList $ [
            FTestPos Lt (Local 2 "firstC") (Local 0 "middleLetter"),
            FTestPos Lt (Local 0 "middleLetter") (Local 1 "nextC") ]
        iIsC       = FLetter (Local 1 "firstC") c1
        jIsC       = FLetter (Local 0 "nextC")  c2

startsWithChar :: Char -> Formula ()
startsWithChar c = quantifyList [("firstC", Pos, Exists)] $ andList [iIsC, isFirst]
    where
        iIsC       = FLetter (Local 0 "firstC") c
        isFirst    = FNot $ quantifyList [("beforeFirst", Pos, Exists)] $ FTestPos Lt (Local 0 "beforeFirst") (Local 1 "firstC")

endsWithChar :: Char -> Formula ()
endsWithChar c = quantifyList [("lastC", Pos, Exists)] $ andList [jIsC, isLast]
    where
        jIsC       = FLetter (Local 0 "lastC") c
        isLast     = FNot $ quantifyList [("afterLast", Pos, Exists)] $ FTestPos Lt (Local 1 "lastC") (Local 0 "afterLast")




higherToSimpleProgram :: Program String ValueType -> SFP.ForProgram
higherToSimpleProgram p = simplifyForProgram sfp
    where
        transformedProg = foldl (flip applyTransform) p transformationsInOrder
        Right sfp = toSimpleForProgram transformedProg

simpleForToInterpretation :: SFP.ForProgram -> Interpretation String
simpleForToInterpretation sfp = Interpretation tags alphabet simplifiedDomain simplifiedOrder labelOrCopy arity
    where
        Interpretation tags alphabet domain order labelOrCopy arity = stringify pathToTag $  toInterpretation sfp
        simplifiedDomain = \s vs -> simplifyFormula $ domain s vs
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
    putStrLn $ "Program: converted to simple for" ++ show simpleForProg
    putStrLn $ "Program: runned on `adb` : " ++ (show $ runProgram simpleForProg "adb")
    let simpleForInterpretation = simpleForToInterpretation simpleForProg
    putStrLn $ "Program: converted to interpretation" ++ show simpleForInterpretation
    putStrLn $ "Program: interpretation runned on `adb` : " ++ (show $ runInterpretation simpleForInterpretation "adb")
    let precondition  = containsAB 'a' 'b'
    let postcondition = containsAB 'a' 'b'
    let hoareTriple = HoareTriple precondition simpleForInterpretation postcondition
    putStrLn $ "Program: transformed to hoare triple" ++ show hoareTriple
    solvers <- installedSolvers
    putStrLn $ "Program: potential solvers " ++ show allSolvers
    putStrLn $ "Program: installed solvers " ++ show solvers
    forM_ solvers $ \solver -> do
        verifyResult <- verifyHoareTriple solver hoareTriple
        putStrLn $ "Program: verified using " ++ show solver
        case verifyResult of
            Unsat     -> putStrLn $ "[" ++ show solver ++ "] YES! The Hoare triple is       valid"
            Sat       -> putStrLn $ "[" ++ show solver ++ "] NO ! The Hoare triple is *not* valid"
            Unknown   -> putStrLn $ "[" ++ show solver ++ "] ???"
            Error msg -> putStrLn $ "[" ++ show solver ++ "] ERROR: " ++ msg


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
