{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveAnyClass #-}
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

import qualified Data.Text as T
import qualified Data.ByteString.Lazy as B
import qualified Data.Text.Encoding as TE


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
import Control.Monad (forM_, mapM_, forM)

import Data.Aeson hiding (Options)
import GHC.Generics

import Data.Maybe (catMaybes)
import System.Directory
import System.Timeout
import System.FilePath ((</>))

import Control.Exception

data Options = Options
    { optInputHL   :: Maybe FilePath
    , optInputDir  :: Maybe FilePath
    , optInputSFP  :: Maybe FilePath
    , optPreCond   :: Maybe FilePath
    , optPostCond  :: Maybe FilePath
    , optHuman     :: Bool
    } deriving (Eq,Show)

options :: Parser Options
options = Options
      <$> optional (strOption (long "input-high-level" <> short 'h' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "input-high-directory" <> short 'd' <> metavar "DIRECTORY" <> help "The input directory"))
      <*> optional (strOption (long "input-simple-for" <> short 's' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "precondition"     <> short 'b' <> metavar "FILE" <> help "The precondition file"))
      <*> optional (strOption (long "postcondition"    <> short 'a' <> metavar "FILE" <> help "The postcondition file"))
      <*> switch (long "human" <> short 'u' <> help "Human readable output")



data BenchmarkSize = BenchmarkSize 
    { bsDepth     :: Int     -- ^ The depth of the program (quantifier depth, number of nested loops)
    , bsSize      :: Int     -- ^ The size of the program (number of instructions)
    , bsCtn       :: String  -- ^ content for debugging purposes
    } deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON)
    
emptySize :: BenchmarkSize
emptySize = BenchmarkSize 0 0 ""

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

-- | Computing Sizes

sizeOfHighLevel p = BenchmarkSize (programDepth p) (programSize p) ""
sizeOfSfp       p = BenchmarkSize (SFP.programDepth p) (SFP.programSize p) "" -- (SFP.prettyPrintForProgram p)
sizeOfInterp    p = BenchmarkSize (maximum . map quantifierDepth $ doms)
                                  (sum . map formulaSize $ doms)
                                  "" -- (prettyPrintFormula $ andList doms)
    where
        doms = do 
            t <- FOI.tags p
            return $ domain p t [In ("x" ++ show i) | i <- [1..]]


parseHL :: String -> Program String ValueType
parseHL inputProg = inputHigh
    where
        inputHigh' = unwrapEither "Parsing Program Failed" $ PHL.parseHighLevel inputProg
        inputHigh  = unwrapEither "Type Inference Failed" $ inferAndCheckProgram inputHigh'


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

handleAny :: (SomeException -> IO a) -> IO a -> IO a 
handleAny h m = Control.Exception.catch m h

highToSfpWithTimeout :: Program String ValueType
                     -> IO (Maybe SFP.ForProgram)
highToSfpWithTimeout high = handleAny (\_ -> return Nothing) $ timeout 5000000 $ do 
        let sfp' = higherToSimpleProgram high
        writeFile  "test.tmp" . SFP.prettyPrintForProgram $ sfp'
        removeFile "test.tmp"
        return sfp'

sfpToIntWithTimeout :: SFP.ForProgram
                    -> IO (Maybe (Interpretation String))
sfpToIntWithTimeout sfp = handleAny (\_ -> return Nothing) $ timeout 5000000  $ do
        let int = simpleForToInterpretation sfp
        writeFile  "test.tmp" . show $ int           
        removeFile "test.tmp"                        
        return int


data BenchmarkFile = BenchmarkFile {
    bfName   :: FilePath,
    bfHigh   :: BenchmarkSize,
    bfSfp    :: Maybe BenchmarkSize,
    bfInterp :: Maybe BenchmarkSize
} deriving (Eq, Show, Generic, ToJSON, FromJSON)

benchmarkHighLevelFile :: FilePath -> IO BenchmarkFile
benchmarkHighLevelFile file = do
    ctn <- readFile file
    let high  = parseHL ctn
    let iSize = sizeOfHighLevel high
    sfp <- highToSfpWithTimeout high
    case sfp of
        Nothing  -> return $ BenchmarkFile file iSize Nothing Nothing
        Just sfp -> do 
            let sSize = sizeOfSfp sfp
            int <- sfpToIntWithTimeout sfp
            case int of
                Nothing  -> return $ BenchmarkFile file iSize (Just sSize) Nothing
                Just int -> return $ BenchmarkFile file iSize (Just sSize) (Just $ sizeOfInterp int)

benchmarkHighLevelFiles :: [FilePath] -> IO [BenchmarkFile]
benchmarkHighLevelFiles files = forM files benchmarkHighLevelFile 

main :: IO ()
main = do 
    opts <- execParser cmdParser
    case optInputDir opts of
        Just dir -> do
            files <- listDirectory dir
            let files' = map (dir </>) files
            benches <- benchmarkHighLevelFiles files'
            putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ benches
        Nothing -> return ()
    case optInputHL opts of
        Just file  -> do
            b <- benchmarkHighLevelFile file
            putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ b
        Nothing -> return ()
