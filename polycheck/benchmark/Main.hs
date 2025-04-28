{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified Data.Text.IO as TIO
import qualified Data.ByteString.Lazy as B
import qualified Data.Text.Encoding as TE
import qualified Data.List as L


import Data.Map (Map)
import qualified Data.Map as M

-- putstrln to stderr
import System.IO (hPutStrLn, stderr)


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

import Data.Aeson hiding (Options, Error)
import GHC.Generics

import Data.Maybe (catMaybes)
import System.Directory
import System.Timeout
import System.FilePath ((</>))

import Control.Exception


import System.Exit


import Control.Monad (when)
import Data.Time.Clock.POSIX (getPOSIXTime)
import Text.Printf (printf)

time :: IO a -> IO (Double, a)
time act = do
  start <- getTime
  result <- act
  end <- getTime
  let !delta = end - start
  return (delta, result)

time_ :: IO a -> IO Double
time_ act = do
  start <- getTime
  _ <- act
  end <- getTime
  return $! end - start

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

runForAtLeast :: Double -> Int -> (Int -> IO a) -> IO (Double, Int, a)
runForAtLeast howLong initSeed act = loop initSeed (0::Int) =<< getTime
  where
    loop !seed !iters initTime = do
      now <- getTime
      when (now - initTime > howLong * 10) $
        fail (printf "took too long to run: seed %d, iters %d" seed iters)
      (elapsed,result) <- time (act seed)
      if elapsed < howLong
        then loop (seed * 2) (iters+1) initTime
        else return (elapsed, seed, result)

secs :: Double -> String
secs k
    | k < 0      = '-' : secs (-k)
    | k >= 1     = k        `with` "s"
    | k >= 1e-3  = (k*1e3)  `with` "ms"
    | k >= 1e-6  = (k*1e6)  `with` "us"
    | k >= 1e-9  = (k*1e9)  `with` "ns"
    | k >= 1e-12 = (k*1e12) `with` "ps"
    | otherwise  = printf "%g s" k
     where with (t :: Double) (u :: String)
               | t >= 1e9  = printf "%.4g %s" t u
               | t >= 1e6  = printf "%.0f %s" t u
               | t >= 1e5  = printf "%.1f %s" t u
               | t >= 1e4  = printf "%.2f %s" t u
               | t >= 1e3  = printf "%.3f %s" t u
               | t >= 1e2  = printf "%.4f %s" t u
               | t >= 1e1  = printf "%.5f %s" t u
               | otherwise = printf "%.6f %s" t u


data Options = Options
    { optInputHL   :: Maybe FilePath
    , optInputDir  :: Maybe FilePath
    , optFormDir   :: Maybe FilePath
    , optTimeout   :: Maybe Int
    , optOutput    :: Maybe FilePath
    , optReproduceTable :: Maybe String
    } deriving (Eq,Show)

options :: Parser Options
options = Options
      <$> optional (strOption (long "input-high-level" <> short 'h' <> metavar "FILE" <> help "The input file"))
      <*> optional (strOption (long "input-high-directory" <> short 'd' <> metavar "DIRECTORY" <> help "The input directory"))
      <*> optional (strOption (long "input-formula-directory" <> short 'f' <> metavar "DIRECTORY" <> help "The input directory for formulas"))
      <*> optional (option auto (long "timeout" <> short 't' <> metavar "TIME" <> help "Timeout in seconds"))
      <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "The output file"))
      <*> optional (strOption (long "reproduce-table" <> short 'r' <> metavar "TABLE" <> help "Reproduce specific table from the paper (can be set to 1 or 2)"))




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
        -- hPutStrLn stderr $ "Simple For Program: " ++ show sfp'
        return $ Right sfp'
highToSfpWithTimeout (Just t) high = handleAny (\e -> return (Left (show e))) $ eitherTimeout t $ do 
        let sfp' = higherToSimpleProgram high
        -- hPutStrLn stderr $ "Simple For Program: " ++ show sfp'
        return sfp'

sfpToIntWithTimeout :: Maybe Int -> SFP.ForProgram
                    -> IO (Either String (Interpretation String))
sfpToIntWithTimeout Nothing sfp = handleAny (\e -> return (Left (show e))) $ do
        let int = simpleForToInterpretation sfp
        -- hPutStrLn stderr $ "Interpretation: " ++ show int
        return $ Right int
sfpToIntWithTimeout (Just t) sfp = handleAny (\e -> return (Left (show e))) $ eitherTimeout t $ do
        let int = simpleForToInterpretation sfp
        -- hPutStrLn stderr $ "Interpretation: " ++ show int
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

data SmtResultBench = SmtOkWithTime String
                    | SmtKoWithTime String
                    | SmtQQWithTime String
                    | SmtTimeout deriving (Eq, Show, Generic, ToJSON, FromJSON)

data BenchmarkSMT = BenchmarkSMT {
    bsmtName        :: FilePath
  , bsmtPre         :: FilePath
  , bsmtPost        :: FilePath
  , bsmtFormula     :: BenchmarkSize
  , bsmtResponses   :: Map String SmtResultBench
} deriving (Eq, Show, Generic, ToJSON, FromJSON)

table1Programs :: [FilePath]
table1Programs = ["identity.pr", "reverse.pr", "subwords_ab.pr", "map_reverse.pr", "prefixes.pr", "get_last_word.pr", "get_first_word.pr", "compress_as.pr", "litteral_test.pr", "bibtex.pr"]

benchmarkSMT :: Maybe Int -> FilePath -> FilePath -> FilePath -> IO (Either String BenchmarkSMT)
benchmarkSMT Nothing prefile progfile postfile = handleAny (\e -> return (Left (show e))) $ do
    pre  <- unwrapEither "Parsing Precondition"  <$> PFO.parseFromFileWithoutTags prefile
    post <- unwrapEither "Parsing Postcondition" <$> PFO.parseFromFileWithoutTags postfile
    high <- parseHL <$> readFile progfile
    let sfp     = higherToSimpleProgram high
    let int     = simpleForToInterpretation sfp
    let hoare   = HoareTriple pre int post
    let formula = encodeHoareTriple hoare
    let size    = BenchmarkSize (quantifierDepth formula) (formulaSize formula) "" 0
    --hPutStrLn stderr $ "Formula: " ++ show size
    solvers <- installedSolvers
    responses <- forM solvers $ \solver -> do
        (d, verifyResult) <- time $ verifyHoareTriple solver hoare
        case verifyResult of
            Unsat     -> return (show solver, SmtOkWithTime (secs d))
            Sat       -> return (show solver, SmtKoWithTime (secs d))
            Unknown   -> return (show solver, SmtQQWithTime (secs d))
            Error msg -> return (show solver, SmtQQWithTime (secs d))
    return $ Right $ BenchmarkSMT progfile prefile postfile size (M.fromList responses)
benchmarkSMT (Just t) prefile progfile postfile = handleAny (\e -> return (Left (show e))) $ do
    pre  <- unwrapEither "Parsing Precondition"  <$> PFO.parseFromFileWithoutTags prefile
    post <- unwrapEither "Parsing Postcondition" <$> PFO.parseFromFileWithoutTags postfile
    high <- parseHL <$> readFile progfile
    --hPutStrLn stderr $ "Parsed " ++ progfile ++ " " ++ prefile ++ " " ++ postfile
    let sfp     = higherToSimpleProgram high
    let int     = simpleForToInterpretation sfp
    let hoare   = HoareTriple pre int post
    let formula = encodeHoareTriple hoare
    let size    = BenchmarkSize (quantifierDepth formula) (formulaSize formula) "" 0
    solvers   <- installedSolvers
    responses <- forM solvers $ \solver -> do
        (d, verifyResult) <- time $ timeout t $ verifyHoareTriple solver hoare
        case verifyResult of
            Just (Unsat     ) -> return (show solver, SmtOkWithTime (secs d))
            Just (Sat       ) -> return (show solver, SmtKoWithTime (secs d))
            Just (Unknown   ) -> return (show solver, SmtQQWithTime (secs d))
            Just (Error msg ) -> return (show solver, SmtQQWithTime (secs d))
            Nothing           -> return (show solver, SmtTimeout)
    return $ Right $ BenchmarkSMT progfile prefile postfile size (M.fromList responses)

---- Produce a table1-style table: 
-- Column headers
headers :: [String]
headers = ["Input File", "HF Size", "HF Loop Depth", "HF Boolean Depth",
           "SF Size", "SF Loop Depth", "SF Boolean Depth",
           "FO Size", "FO Quantifier Rank"]

-- Produce a row for each benchmark
benchmarkToRow :: BenchmarkFile -> [String]
benchmarkToRow bf =
  let (sfSize, sfDepth, sfBoolDepth) = showSfp (bfSfp bf)
      (foSize, foQuantDepth) = showInterp (bfInterp bf)
      hf = bfHigh bf
  in [ bfName bf
     , show (bsSize hf)
     , show (bsDepth hf)
     , show (bsBoolDepth hf)
     , sfSize
     , sfDepth
     , sfBoolDepth
     , foSize
     , foQuantDepth
     ]

showSfp :: Either String BenchmarkSize -> (String, String, String)
showSfp (Right bs) = (show (bsSize bs), show (bsDepth bs), show (bsBoolDepth bs))
showSfp (Left _)   = ("-", "-", "-")

showInterp :: Either String BenchmarkSize -> (String, String)
showInterp (Right bs) = (show (bsSize bs), show (bsDepth bs))
showInterp (Left _)   = ("-", "-")

-- Join fields into one Markdown line
formatRow :: [String] -> String
formatRow fields = "| " ++ L.intercalate " | " fields ++ " |"

-- Markdown separator row
markdownSeparator :: Int -> String
markdownSeparator n = "|" ++ L.intercalate "|" (replicate n " --- ") ++ "|"

-- The main function you want
generateMarkdownTable :: [BenchmarkFile] -> String
generateMarkdownTable benchmarks =
  let allRows = map benchmarkToRow benchmarks
      headerRow = formatRow headers
      separatorRow = markdownSeparator (length headers)
      dataRows = map formatRow allRows

      headerExplanation = unlines
        [ "HF = High-Level Form, SF = Simple Form, FO = FO transduction."
        , ""
        ]

  in unlines (headerExplanation : headerRow : separatorRow : dataRows)



main :: IO ()
main = do 
    opts <- execParser cmdParser
    case (optReproduceTable opts) of
        Just "1" -> do
            let files = map (\f -> "assets/HighLevel/" ++ f) table1Programs
            BenchmarkMetadata benches <- benchmarkHighLevelFiles Nothing files
            case (optOutput opts) of
                Just file -> do
                    putStrLn $ generateMarkdownTable benches
                    exitSuccess
                Nothing -> do 
                    putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ benches
                    exitSuccess
        _ -> return ()
    let timeoutMilisec = (*1000000) <$> optTimeout opts
    case (optFormDir opts, optInputDir opts) of
        (Nothing, _) -> return ()
        (_, Nothing) -> return ()
        (Just dirF, Just dirH) -> do 
            filesF <- listDirectory dirF
            filesH <- listDirectory dirH
            let filesF' = map (dirF </>) filesF
            let filesH' = map (dirH </>) filesH
            let triples = [(f, h, p) | f <- filesF', h <- filesH', p <- filesF']
            benches <- forM triples (\(pre, prog, post) -> benchmarkSMT timeoutMilisec pre prog post)
            case (optOutput opts) of
                Just file -> do
                    TIO.writeFile file . TE.decodeUtf8 . B.toStrict . encode $ benches
                    exitSuccess
                Nothing -> do
                    putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ benches
                    exitSuccess
    case optInputDir opts of
        Just dir -> do
            files <- listDirectory dir
            let files' = map (dir </>) files
            benches <- benchmarkHighLevelFiles timeoutMilisec files'
            case (optOutput opts) of
                Just file -> do
                    TIO.writeFile file . TE.decodeUtf8 . B.toStrict . encode $ benches
                    exitSuccess
                Nothing -> do 
                    putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ benches
                    exitSuccess
        Nothing -> return ()
    case optInputHL opts of
        Just file  -> do
            b <- benchmarkHighLevelFile timeoutMilisec file
            case (optOutput opts) of
                Just file -> do
                    TIO.writeFile file . TE.decodeUtf8 . B.toStrict . encode $ b
                    exitSuccess
                Nothing -> do
                    putStrLn . T.unpack . TE.decodeUtf8 . B.toStrict . encode $ b
                    exitSuccess
        Nothing -> return ()
