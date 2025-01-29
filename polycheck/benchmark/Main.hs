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
import qualified Parser.ParseSimple     as PS


import ForPrograms.HighLevel.Typing(ValueType(..))

import Logic.HoareTriple    (HoareTriple(..), verifyHoareTriple, encodeHoareTriple)
import Logic.Export         (PossibleSolvers, 
                             ExportResult(..), 
                             EncodeParams(..), 
                             allSolvers,
                             installedSolvers)
import Logic.Interpreter    (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))
import qualified Logic.Interpretation as FOI

import Logic.Formulas (simplifyFormula, prettyPrintFormula, andList, Formula, quantifierDepth, formulaSize, Var(..))
import Logic.FormulaExamples
import Logic.FormulaChecker (checkFormulaTypes, TypeError(..))

import Options.Applicative
import Control.Monad (forM_)

data Options = Options
    { optInputHL   :: Maybe FilePath
    , optInputSFP  :: Maybe FilePath
    , optPreCond   :: Maybe FilePath
    , optPostCond  :: Maybe FilePath
    } deriving (Eq,Show)

options :: Parser Options
options = Options
      <$> optional (strOption (long "input-high-level" <> short 'h' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "input-simple-for" <> short 's' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "precondition"  <> short 'b' <> metavar "FILE" <> help "The precondition file"))
      <*> optional (strOption (long "postcondition" <> short 'a' <> metavar "FILE" <> help "The postcondition file"))


data BenchmarkSize = BenchmarkSize 
    { bsDepth     :: Int     -- ^ The depth of the program (quantifier depth, number of nested loops)
    , bsSize      :: Int     -- ^ The size of the program (number of instructions)
    , bsCtn       :: String  -- ^ content for debugging purposes
    } deriving (Eq,Show)

data BenchmarkTransform = BenchmarkTransform
    { btInput   :: BenchmarkSize
    , btOutput  :: BenchmarkSize
    } deriving (Eq,Show)

higherToSimpleProgram :: Program String ValueType -> SFP.ForProgram
higherToSimpleProgram p = simplifyForProgram sfp
    where
        transformedProg = foldl (flip applyTransform) p transformationsInOrder
        Right sfp = toSimpleForProgram transformedProg


benchHtoS :: String -> BenchmarkTransform
benchHtoS inputProg = BenchmarkTransform sizeInput sizeOutput
    where
        inputHigh' = unwrapEither "Parsing Program Failed" $ PHL.parseHighLevel inputProg
        inputHigh  = unwrapEither "Type Inference Failed" $ inferAndCheckProgram inputHigh'
        ctnInput   = inputProg
        sizeInput  = BenchmarkSize (programDepth inputHigh) (programSize inputHigh) ctnInput
        transformedProg = higherToSimpleProgram inputHigh
        sizeOutput = BenchmarkSize (SFP.programDepth transformedProg) (SFP.programSize transformedProg) ctnOuptut
        ctnOuptut  = SFP.prettyPrintForProgram transformedProg

simpleForToInterpretation :: SFP.ForProgram -> Interpretation String
simpleForToInterpretation sfp = Interpretation tags alphabet simplifiedDomain simplifiedOrder labelOrCopy arity
    where
        Interpretation tags alphabet domain order labelOrCopy arity = stringify pathToTag $  toInterpretation sfp
        simplifiedDomain = \s vs -> simplifyFormula $ domain s vs
        simplifiedOrder  = \s1 s2 vs1 vs2 -> simplifyFormula $ order s1 s2 vs1 vs2


benchStoI :: String -> BenchmarkTransform
benchStoI inputProg = BenchmarkTransform sizeInput sizeOutput
    where
        inputSfp = unwrapEither "Parsing SFP Failed" $ PS.parseSimpleForProgram inputProg
        sizeInput = BenchmarkSize (SFP.programDepth inputSfp) (SFP.programSize inputSfp) inputProg
        interpretation = simpleForToInterpretation inputSfp
        doms = do 
            t <- FOI.tags interpretation
            return $ domain interpretation t [In ("x" ++ show i) | i <- [1..]]
        sizeOutput = BenchmarkSize (maximum . map quantifierDepth $ doms)
                                   (sum . map formulaSize $ doms)
                                   (prettyPrintFormula $ andList doms)

cmdParser :: ParserInfo Options
cmdParser = info (options <**> helper)
    ( fullDesc
    <> progDesc "Formal verification of programs."
    <> header "Policzek -- *Benchmark Maker*" )



unwrapEither :: (Show b) => String -> Either b a -> a
unwrapEither ctx (Left err) = error $ "[" ++ ctx ++ "]" ++ "Error: " ++ show err
unwrapEither ctx (Right x) = x

unwrapMaybe :: String -> Maybe a -> a
unwrapMaybe ctx (Just x) = x
unwrapMaybe ctx Nothing = error $ "[" ++ ctx ++ "]" ++ "Error: Nothing"


typeCheckFormula :: Formula t -> IO (Formula t)
typeCheckFormula f = do
    let checked = checkFormulaTypes f
    case checked of
        Left err -> error $ "Type error: " ++ show err
        Right _  -> return f


main :: IO ()
main = do 
    opts <- execParser cmdParser
    case optInputHL opts of
        Just file  -> do
            ctn <- readFile file
            let (BenchmarkTransform (BenchmarkSize id is ic) (BenchmarkSize od os oc)) = benchHtoS ctn
            putStrLn $ "Benchmark [" ++ show file ++ "] depth: " ++ show id ++ " -> " ++ show od
            putStrLn $ "Benchmark [" ++ show file ++ "] size: " ++ show is ++ " -> " ++ show os
            putStrLn $ ic
            putStrLn $ "----------------"
            putStrLn $ oc
        Nothing -> return ()
    case optInputSFP opts of
        Just file  -> do
            ctn <- readFile file
            let bench = benchStoI ctn
            putStrLn $ "Benchmark: " ++ show bench
        Nothing -> return ()
