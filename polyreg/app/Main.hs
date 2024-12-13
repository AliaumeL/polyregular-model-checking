module Main (main) where


import ForPrograms
import ForProgramsTyping (ValueType(..))
import Typing.Inference (inferAndCheckProgram)
import ForProgramInterpreter (runProgramString)
import BooleanElimination (removeBooleanGen)
import FunctionElimination (eliminateFunctionCalls)
import LiteralElimination (eliminateLiterals)
import LetElimination (eliminateLetProgram)
import ForLoopExpansion (forLoopExpansion)
import ReturnElimination (retElimProgram)
import ReductionLitEq (removeBLitEq)
import ForProgramsPrettyPrint
import Parser.ParseHighLevel (parseHighLevel)

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


data Transformation = LitEqElimination
                    | FunctionElimination
                    | LiteralElimination    -- litteral to generators
                    | BooleanElimination
                    | ReturnElimination
                    | LetOutputElimination
                    | ForLoopExpansion
                    deriving (Eq,Show,Read,Ord,Enum)

transformationsInOrder :: [Transformation]
transformationsInOrder = [LitEqElimination .. ForLoopExpansion]


applyTransform :: Transformation -> Program String ValueType -> Program String ValueType
applyTransform BooleanElimination p = removeBooleanGen p
applyTransform FunctionElimination p = eliminateFunctionCalls p
applyTransform LiteralElimination p = eliminateLiterals p
applyTransform LitEqElimination p = removeBLitEq p
applyTransform LetOutputElimination p = eliminateLetProgram p
applyTransform ReturnElimination p = retElimProgram p
applyTransform ForLoopExpansion p = case forLoopExpansion p of  
    Left err -> error $ "Error in for loop expansion: " ++ show err
    Right p' -> p'


data Options = Options
    { optInputProg :: Maybe FilePath
    , optInputWord :: Maybe String
    , optTransformations :: Maybe Int
    , optOutputProg :: Maybe FilePath
    , optOutputWord :: Maybe String
    , optList :: Bool
    } deriving (Eq,Show)

options :: Parser Options
options = Options
    <$> optional (strOption (long "input-prog" <> short 'i' <> metavar "FILE" <> help "The input file"))
    <*> optional (strOption (long "input-word" <> short 'w' <> metavar "WORD" <> help "The input word"))
    <*> optional (option auto (long "transformation" <> short 't' <> metavar "TRANSFORMATION" <> help "The transformation to apply"))
    <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "The output file"))
    <*> optional (strOption (long "output-word" <> short 'W' <> metavar "WORD" <> help "The output word"))
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


untypeExceptFunctions :: Program String ValueType -> Program String (Maybe ValueType)
untypeExceptFunctions (Program fs main) = Program (map untypeFun fs) main 
    where
        untypeFun (StmtFun name args s t) = StmtFun name (map (\(a,t,ps) -> (a, Just t, ps)) args) (fmap (const Nothing) s) (Just t)


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
                    case inferAndCheckProgram (fmap erasePositionTypes transformedProg) of
                        Left err ->  
                            case inferAndCheckProgram (untypeExceptFunctions transformedProg) of
                                Left err -> putStrLn $ "Program stopped typechecking (all together!)" ++ show err
                                Right _  -> putStrLn $ "Program stopped typechecking (with our types, but otherwise it is fine) " ++ show err
                        Right _  -> putStrLn $ "Program still type checks"
                    case word of
                        Nothing -> return ()
                        Just w -> do
                            let wordBefore = runProgramString (fmap (const ()) prog) w
                            let wordAfter  = runProgramString (fmap (const ()) transformedProg) w
                            writeOutputFile (optOutputWord opts) (replicate 80 '-')
                            writeOutputFile (optOutputWord opts) w
                            writeOutputFile (optOutputWord opts) (show wordBefore)
                            writeOutputFile (optOutputWord opts) (show wordAfter)
                            writeOutputFile (optOutputWord opts) ("Is the same: " ++ (show $ wordBefore == wordAfter))
