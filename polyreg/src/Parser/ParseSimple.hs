module Parser.ParseSimple where

import Parser.SimpleForProgram.Par   ( pProgram, myLexer )
import Parser.ParsedToSimpleForProgram ( parsedToForProgram )
import SimpleForPrograms


parseHighLevel :: String -> Either String ForProgram
parseHighLevel s = do
    case pProgram (myLexer s) of
        Left err -> Left $ show err
        Right p -> Right $ parsedToForProgram p

parseFromFile :: FilePath -> IO (Either String ForProgram)
parseFromFile path = do
    s <- readFile path
    return $ parseHighLevel s