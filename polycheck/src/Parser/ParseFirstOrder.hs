module Parser.ParseFirstOrder where

import Parser.FirstOrderLogic.Par   ( pFormula, myLexer )
import Parser.ParsedToFirstOrderLogic ( parsedToFirstOrderLogic )
import Logic.Formulas

parseFirstOrderFormula :: String -> Either String (Formula String)
parseFirstOrderFormula s = do
    case pFormula (myLexer s) of
        Left err -> Left $ show err
        Right p -> Right $ parsedToFirstOrderLogic p


parseWithoutTags :: String -> Either String (Formula ())
parseWithoutTags s = do 
    f <- parseFirstOrderFormula s
    removeTags f

parseFromFile :: FilePath -> IO (Either String (Formula String))
parseFromFile path = do
    s <- readFile path
    return $ parseFirstOrderFormula s

parseFromFileWithoutTags :: FilePath -> IO (Either String (Formula ()))
parseFromFileWithoutTags path = do
    s <- readFile path
    return $ parseWithoutTags s
