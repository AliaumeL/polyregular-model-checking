module Parser.ParseHighLevel where

import Parser.HighLevelForProgram.Par   ( pProgram, myLexer )
import Parser.ParsedToForProgram ( parsedToForProgram )
import ForPrograms

parseHighLevel :: String -> Either String UProgram
parseHighLevel s = do
    case pProgram (myLexer s) of
        Left err -> Left $ show err
        Right p -> parsedToForProgram p


