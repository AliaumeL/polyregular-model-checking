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
    , optTimeout   :: Maybe Int
    } deriving (Eq,Show)

options :: Parser Options
options = Options
      <$> optional (strOption (long "input-high-level" <> short 'h' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "input-high-directory" <> short 'd' <> metavar "DIRECTORY" <> help "The input directory"))
      <*> optional (strOption (long "input-simple-for" <> short 's' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "precondition"     <> short 'b' <> metavar "FILE" <> help "The precondition file"))
      <*> optional (strOption (long "postcondition"    <> short 'a' <> metavar "FILE" <> help "The postcondition file"))
      <*> switch (long "human" <> short 'u' <> help "Human readable output")
      <*> optional (option auto (long "timeout" <> short 't' <> metavar "TIME" <> help "Timeout in seconds"))



data BenchmarkSize = BenchmarkSize 
    { bsDepth     :: Int     -- ^ The depth of the program (quantifier depth, number of nested loops)
    , bsSize      :: Int     -- ^ The size of the program (number of instructions)
    , bsCtn       :: String  -- ^ content for debugging purposes
    , bsBoolDepth :: Int     -- ^ The depth of the boolean formula
    } deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON)
    
emptySize :: BenchmarkSize
emptySize = BenchmarkSize 0 0 "" 0

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

sizeOfHighLevel p = BenchmarkSize (programDepth p) (programSize p) "" (programBoolDepth p)
sizeOfSfp       p = BenchmarkSize (SFP.programDepth p) (SFP.programSize p) "" (SFP.programBoolDepth p)
sizeOfInterp    p = BenchmarkSize (maximum . map quantifierDepth $ doms)
                                  (sum . map formulaSize $ doms)
                                  "" -- (prettyPrintFormula $ andList doms)
                                  0
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

eitherTimeout :: Int -> IO a -> IO (Either String a)
eitherTimeout t m = do
    res <- timeout t m
    case res of
        Nothing -> return $ Left "Timeout"
        Just x  -> return $ Right x

highToSfpWithTimeout :: Maybe Int -> Program String ValueType
                     -> IO (Either String SFP.ForProgram)
highToSfpWithTimeout Nothing high = handleAny (\e -> return (Left (show e))) $ do
        let sfp' = higherToSimpleProgram high
        return $ Right sfp'
highToSfpWithTimeout (Just t) high = handleAny (\e -> return (Left (show e))) $ eitherTimeout t $ do 
        let sfp' = higherToSimpleProgram high
        writeFile  "test.tmp" . SFP.prettyPrintForProgram $ sfp'
        removeFile "test.tmp"
        return sfp'

sfpToIntWithTimeout :: Maybe Int -> SFP.ForProgram
                    -> IO (Either String (Interpretation String))
sfpToIntWithTimeout Nothing sfp = handleAny (\e -> return (Left (show e))) $ do
        let int = simpleForToInterpretation sfp
        return $ Right int
sfpToIntWithTimeout (Just t) sfp = handleAny (\e -> return (Left (show e))) $ eitherTimeout t $ do
        let int = simpleForToInterpretation sfp
        writeFile  "test.tmp" . show $ int           
        removeFile "test.tmp"                        
        return int


data BenchmarkFile = BenchmarkFile {
    bfName   :: FilePath,
    bfHigh   :: BenchmarkSize,
    bfSfp    :: Either String BenchmarkSize,
    bfInterp :: Either String BenchmarkSize
} deriving (Eq, Show, Generic, ToJSON, FromJSON)


data BenchmarkMetadata = BenchmarkMetadata {
    benches :: [BenchmarkFile]
} deriving (Eq, Show, Generic, ToJSON, FromJSON)

benchmarkHighLevelFile :: Maybe Int -> FilePath -> IO BenchmarkFile
benchmarkHighLevelFile t file = do
    ctn <- readFile file
    let high  = parseHL ctn
    let iSize = sizeOfHighLevel high
    sfp <- highToSfpWithTimeout t high
    case sfp of
        Left  err -> return $ BenchmarkFile file iSize (Left err) (Left "-")
        Right sfp -> do 
            let sSize = sizeOfSfp sfp
            int <- sfpToIntWithTimeout t sfp
            case int of
                Left err  -> return $ BenchmarkFile file iSize (Right sSize) (Left err)
                Right int -> return $ BenchmarkFile file iSize (Right sSize) (Right $ sizeOfInterp int)

benchmarkHighLevelFiles :: Maybe Int -> [FilePath] -> IO BenchmarkMetadata
benchmarkHighLevelFiles t files = BenchmarkMetadata <$> forM files (benchmarkHighLevelFile t)

main :: IO ()
main = do 
    opts <- execParser cmdParser
    let timeoutMilisec = (*1000000) <$> optTimeout opts
    case optInputDir opts of
        Just dir -> do
            files <- listDirectory dir
            let files' = map (dir </>) files
            benches <- benchmarkHighLevelFiles timeoutMilisec files'
            putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ benches
        Nothing -> return ()
    case optInputHL opts of
        Just file  -> do
            b <- benchmarkHighLevelFile timeoutMilisec file
            putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ b
        Nothing -> return ()
