module Parser.ParseHighLevel where

import Parser.HighLevelForProgram.Par   ( pProgram, myLexer )
import Parser.ParsedToForProgram ( parsedToForProgram, PAProgram )
import ForPrograms

parseHighLevel :: String -> Either String PAProgram
parseHighLevel s = do
    case pProgram (myLexer s) of
        Left err -> Left $ show err
        Right p -> parsedToForProgram p


