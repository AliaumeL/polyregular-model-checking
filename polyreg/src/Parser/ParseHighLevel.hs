module Parser.ParseHighLevel where

import Parser.HighLevelForProgram.Par   ( pProgram, myLexer )
import Parser.ParsedToForProgram ( parsedToForProgram )
import ForPrograms
import qualified ForProgramsTyping as T

type PartiallyTypedProgram = Program String (Maybe T.ValueType)

parseHighLevel :: String -> Either String PartiallyTypedProgram
parseHighLevel s = do
    case pProgram (myLexer s) of
        Left err -> Left $ show err
        Right p -> parsedToForProgram p

parseFromFile :: FilePath -> IO (Either String PartiallyTypedProgram)
parseFromFile path = do
    s <- readFile path
    return $ parseHighLevel s

