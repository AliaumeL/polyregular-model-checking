module Main (main) where


import ForPrograms.HighLevel

import ForPrograms.HighLevel.Interpreter (runProgramString, InterpretError(..))
import ForPrograms.HighLevel.Typing.Inference   (inferAndCheckProgram)
import ForPrograms.HighLevel.Transformations    (applyTransform, transformationsInOrder)
import ForPrograms.HighLevel.ToSimple (toSimpleForProgram)
import ForPrograms.Simple (runProgram, pathToTag)
import qualified ForPrograms.Simple as SFP
import ForPrograms.Simple.Optimization(simplifyForProgram)


import qualified Parser.ParseFirstOrder as PFO
import qualified Parser.ParseHighLevel  as PHL


import ForPrograms.HighLevel.Typing(ValueType(..))

import Logic.HoareTriple    (HoareTriple(..), verifyHoareTriple, encodeHoareTriple)
import Logic.Export         (ExportResult(..), EncodeParams(..), allSolvers, installedSolvers)
import Logic.Interpreter    (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))

import Logic.Formulas (simplifyFormula, Formula)
import Logic.FormulaExamples
import Logic.FormulaChecker (checkFormulaTypes, TypeError(..))

import Options.Applicative
import Control.Monad (forM_)

import Web.API (webApp)


data Options = Options
    { optInputProg :: Maybe FilePath
    , optPreCond   :: Maybe FilePath
    , optPostCond  :: Maybe FilePath
    , optWeb :: Bool
    } deriving (Eq,Show)

options :: Parser Options
options = Options
      <$> optional (strOption (long "input-prog"    <> short 'i' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "precondition"  <> short 'b' <> metavar "FILE" <> help "The precondition file"))
      <*> optional (strOption (long "postcondition" <> short 'a' <> metavar "FILE" <> help "The postcondition file"))
      <*> switch   (long "web" <> short 'w' <> help "Start the web server")


cmdParser :: ParserInfo Options
cmdParser = info (options <**> helper)
    ( fullDesc
    <> progDesc "Formal verification of programs."
    <> header "Policzek" )

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


unwrapEither :: (Show b) => String -> Either b a -> IO a
unwrapEither ctx (Left err) = error $ "[" ++ ctx ++ "]" ++ "Error: " ++ show err
unwrapEither ctx (Right x) = return x

unwrapMaybe :: String -> Maybe a -> IO a
unwrapMaybe ctx (Just x) = return x
unwrapMaybe ctx Nothing = error $ "[" ++ ctx ++ "]" ++ "Error: Nothing"


typeCheckFormula :: Formula t -> IO (Formula t)
typeCheckFormula f = do
    let checked = checkFormulaTypes f
    case checked of
        Left err -> error $ "Type error: " ++ show err
        Right _  -> return f

cliApp :: Options -> IO ()
cliApp opts = do
    parsedProg <- unwrapMaybe "Program file" (optInputProg opts) 
                        >>= PHL.parseFromFile 
                        >>= unwrapEither "Parsing Program"
    precond    <- unwrapMaybe "Postcondition file" (optPreCond opts)
                        >>= PFO.parseFromFileWithoutTags 
                        >>= unwrapEither "Parsing Precondition"
                        >>= typeCheckFormula
    postcond   <- unwrapMaybe "Postcondition file" (optPostCond opts)
                        >>= PFO.parseFromFileWithoutTags
                        >>= unwrapEither "Parsing Postcondition"
                        >>= typeCheckFormula
    typedProg  <- unwrapEither "Typing" $ inferAndCheckProgram parsedProg
    let simpleForProg           = higherToSimpleProgram typedProg
    putStrLn $ "Program: converted to simple for:\n" ++ SFP.prettyPrintForProgram simpleForProg ++ "\n"
    putStrLn $ "Program: ran on `adb` : " ++ (show $ runProgram simpleForProg "adb")
    let simpleForInterpretation = simpleForToInterpretation simpleForProg
    putStrLn $ "Program: converted to interpretation" ++ show simpleForInterpretation
    putStrLn $ "Program: interpretation ran on `adb` : " ++ (show $ runInterpretation simpleForInterpretation "adb")
    let hoareTriple   = HoareTriple precond simpleForInterpretation postcond 
    putStrLn $ "Program: transformed to hoare triple" ++ show hoareTriple
    solvers <- installedSolvers
    putStrLn $ "Program: potential solvers " ++ show allSolvers
    putStrLn $ "Program: installed solvers " ++ show solvers
    forM_ solvers $ \solver -> do
        verifyResult <- verifyHoareTriple solver hoareTriple
        putStrLn $ "Program: verified using " ++ show solver
        case verifyResult of
            Unsat     -> putStrLn $ "[" ++ show solver ++ "] OK ! The Hoare triple is       valid"
            Sat       -> putStrLn $ "[" ++ show solver ++ "] KO ! The Hoare triple is *not* valid"
            Unknown   -> putStrLn $ "[" ++ show solver ++ "] ?? ! The Hoare triple is       unknown"
            Error msg -> putStrLn $ "[" ++ show solver ++ "] ERROR: " ++ msg

main :: IO ()
main = do 
    opts <- execParser cmdParser
    case optWeb opts of
        True  -> webApp
        False -> cliApp opts
