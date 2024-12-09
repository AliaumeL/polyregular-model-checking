module Main (main) where


import ForPrograms
import ForProgramsTyping
import ForProgramInterpreter
import BooleanElimination (removeBooleanGen)
import FunctionElimination (eliminateFunctionCalls)
import LiteralElimination (eliminateLiterals)
import ForLoopExpansion (expandGenStmt, ExtVars(..), mapVarsProgram, mapVars)
import ReductionLitEq (removeBLitEq)
import ForProgramsPrettyPrint
import Parser.ParseHighLevel (parseHighLevel)

import Options.Applicative

import Control.Monad
import Control.Applicative

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


data Transformation = BooleanElimination
                    | FunctionElimination
                    | LiteralElimination
                    | ReductionLitEq
                    | ForLoopExpansion
                    deriving (Eq,Show,Read)

applyTransform :: Transformation -> Program String ValueType -> Program String ValueType
applyTransform BooleanElimination p = removeBooleanGen p
applyTransform FunctionElimination p = eliminateFunctionCalls p
applyTransform LiteralElimination p = eliminateLiterals p
applyTransform ReductionLitEq p = removeBLitEq p
applyTransform ForLoopExpansion (Program funcs main) = newProgClassicalVars
    where
        (StmtFun v args body t) = last funcs
        noGenerators = expandGenStmt (mapVars OldVar body)
        newArgs = map (\(n, t, ps) -> (OldVar n, t, map OldVar ps)) args
        newName = OldVar v
        newProg = Program [StmtFun newName newArgs noGenerators t] newName
        newProgClassicalVars = mapVarsProgram (\(OldVar v) -> v) newProg


data Options = Options
    { optInput :: Maybe FilePath
    , optTransformations :: [Transformation]
    , optOutput :: Maybe FilePath
    , optList :: Bool
    } deriving (Eq,Show)

options :: Parser Options
options = Options
    <$> optional (strOption (long "input" <> short 'i' <> metavar "FILE" <> help "The input file"))
    <*> many (option auto (long "transformation" <> short 't' <> metavar "TRANSFORMATION" <> help "The transformations to apply"))
    <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "The output file"))
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

main :: IO ()
main = do
    opts <- execParser cmdParser
    progString <- readInputFile (optInput opts)
    let parsedProgOrErr  = parseHighLevel progString 
    case parsedProgOrErr of
        Left err -> putStrLn . show $ err
        Right parsedProg -> do 
            let typedProg = inferProgram parsedProg
            case typedProg of
                Left err -> putStrLn . show $ err
                Right prog -> do
                    let transformations = optTransformations opts
                    let transformedProg = foldl (flip applyTransform) prog transformations
                    writeOutputFile (optOutput opts) (prettyPrintProgramWithNls transformedProg)
                    return ()
