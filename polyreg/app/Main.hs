module Main (main) where


import ForPrograms.HighLevel

import Parser.ParseHighLevel (parseHighLevel)
import ForPrograms.HighLevel.Interpreter (runProgramString, InterpretError(..))
import ForPrograms.HighLevel.Typing.Inference   (inferAndCheckProgram)
import ForPrograms.HighLevel.Transformations    (applyTransform, transformationsInOrder)
import ForPrograms.HighLevel.ToSimple (toSimpleForProgram)
import ForPrograms.Simple (runProgram, pathToTag)
import qualified ForPrograms.Simple as SFP
import ForPrograms.Simple.Optimization(simplifyForProgram)


import ForPrograms.HighLevel.Typing(ValueType(..))

import Logic.HoareTriple    (HoareTriple(..), verifyHoareTriple, encodeHoareTriple)
import Logic.Export         (ExportResult(..), EncodeParams(..), allSolvers, installedSolvers)
import Logic.Interpreter    (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))

import Logic.Formulas (simplifyFormula)
import Logic.FormulaExamples

import Options.Applicative
import Control.Monad (forM_)

import Web.API (webApp)


data Options = Options
    { optInputProg :: Maybe FilePath
    , optInputWord :: Maybe String
    , optTransformations :: Maybe Int
    , optOutputProg :: Maybe FilePath
    , optOutputWord :: Maybe String
    , optNoSimplify :: Bool
    , optList :: Bool
    , optWeb :: Bool
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
      <*> switch   (long "web" <> short 'b' <> help "Start the web server")



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

cliApp :: Options -> IO ()
cliApp opts = do
    progString <- readInputFile (optInputProg opts)
    putStrLn $ "Program: read"
    let parsedProg'             = parseHighLevel progString
    let parsedProg = case parsedProg' of
        Left err -> putStrLn $ "Error: " ++ err
        Right parsedProg -> parsedProg
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

main :: IO ()
main = do 
    opts <- execParser cmdParser
    case optWeb opts of
        True  -> webApp
        False -> cliApp opts
