module Parser.ParseSimple where

import Parser.SimpleForProgram.Par   ( pProgram, myLexer )
import Parser.ParsedToSimpleForProgram ( parsedToForProgram )
import ForPrograms.Simple

parseSimpleForProgram :: String -> Either String ForProgram
parseSimpleForProgram s = do
    case pProgram (myLexer s) of
        Left err -> Left $ show err
        Right p -> Right $ parsedToForProgram p

parseFromFile :: FilePath -> IO (Either String ForProgram)
parseFromFile path = do
    s <- readFile path
    return $ parseSimpleForProgram s