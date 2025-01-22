{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}

module Web.API (webApp) where

import GHC.Generics
import Data.Aeson (FromJSON, ToJSON)


import Web.Scotty

import System.Directory (getDirectoryContents)

import Logic.Export (ExportResult(..), 
                     PossibleSolvers(..), 
                     EncodeParams(..), 
                     encodeAndRun, 
                     allSolvers, 
                     solverIsInstalled,
                     installedSolvers)

import ForPrograms.HighLevel.Transformations    (applyTransform, transformationsInOrder)
import ForPrograms.HighLevel.ToSimple (toSimpleForProgram)
import ForPrograms.Simple (runProgram, pathToTag)
import qualified ForPrograms.Simple as SFP
import ForPrograms.Simple.Optimization(simplifyForProgram)
import ForPrograms.HighLevel (Program)
import ForPrograms.HighLevel.Typing.Inference   (inferAndCheckProgram)
import ForPrograms.HighLevel.Typing(ValueType(..))
import Parser.ParseHighLevel (parseHighLevel,PartiallyTypedProgram)
import ForPrograms.Simple (prettyPrintForProgram)

import Logic.HoareTriple    (HoareTriple(..), verifyHoareTriple, encodeHoareTriple)
import Logic.Export         (ExportResult(..), EncodeParams(..), allSolvers, installedSolvers)
import Logic.Interpreter    (runInterpretation)
import Logic.Interpretation (toInterpretation, stringify, Interpretation (..))

import Logic.Formulas 
import Logic.FormulaExamples

data VerifyRequest = VerifyRequest {
    program  :: String,
    precond  :: String,
    postcond :: String
} deriving (Show, Eq, Generic, FromJSON, ToJSON)

data SolverResponse = SolverResponse {
    solverUsed :: String,
    answer     :: String
} deriving (Show, Eq, Generic, FromJSON, ToJSON)


data VerifyResponse = VerifyResponse {
    request     :: VerifyRequest,
    errorMsg    :: String,
    simplified  :: String,
    responses   :: [SolverResponse]
} deriving (Eq, Show, Generic, FromJSON, ToJSON)

data SolverStatus = SolverStatus {
    solverName   :: String,
    solverStatus :: String
} deriving (Show, Eq, Generic, FromJSON, ToJSON)

data SolverList = SolverList {
    solvers :: [SolverStatus]
} deriving (Show, Eq, Generic, FromJSON, ToJSON)

data AssetContent = AssetContent {
    name :: String,
    content :: String
} deriving (Show, Eq, Generic, FromJSON, ToJSON)

data AssetList = AssetList {
    assets :: [AssetContent]
} deriving (Show, Eq, Generic, FromJSON, ToJSON)

inferAndCheckProgram' :: PartiallyTypedProgram -> Either String (Program String ValueType)
inferAndCheckProgram' p = case inferAndCheckProgram p of 
    Left err -> Left $ show err
    Right p  -> Right p

toSimpleForProgram' :: Program String ValueType -> Either String SFP.ForProgram
toSimpleForProgram' p = case toSimpleForProgram p of 
    Left err -> Left $ show err
    Right p  -> Right p

simpleForToInterpretation :: SFP.ForProgram -> Interpretation String
simpleForToInterpretation sfp = Interpretation tags alphabet simplifiedDomain simplifiedOrder labelOrCopy arity
    where
        Interpretation tags alphabet domain order labelOrCopy arity = stringify pathToTag $  toInterpretation sfp
        simplifiedDomain = \s vs -> simplifyFormula $ domain s vs
        simplifiedOrder  = \s1 s2 vs1 vs2 -> simplifyFormula $ order s1 s2 vs1 vs2


parseVerifyRequest :: VerifyRequest -> Either String (HoareTriple, SFP.ForProgram)
parseVerifyRequest (VerifyRequest p σ τ) = do
    partiallyTyped <- parseHighLevel p
    typed          <- inferAndCheckProgram' partiallyTyped
    let transformedProg = foldl (flip applyTransform) typed transformationsInOrder
    simple         <- toSimpleForProgram' transformedProg
    let interpreted = simpleForToInterpretation simple
    
    -- remove extra whitespace for τ and σ and then read them as formulas
    let precond    = read σ
    let postcond   = read τ
    return $ (HoareTriple (precond) interpreted (postcond), simple)

getAssetContent :: String -> String -> IO AssetContent
getAssetContent prefix path = do
    content <- readFile $ prefix ++ "/" ++ path
    return $ AssetContent path content

startsWith :: String -> String -> Bool
startsWith [] [] = True
startsWith []  _ = False
startsWith _  [] = True
startsWith (x:xs) (y:ys) = x == y && startsWith xs ys


listDirectoryAssets :: String -> IO AssetList
listDirectoryAssets path = do
    alist <- getDirectoryContents path
    cnts  <- mapM (getAssetContent path) $ filter (\a -> not( a `startsWith` ".")) alist
    return $ AssetList cnts


webApp :: IO ()
webApp = scotty 3000 $ do
  get "/style.css" $ do 
    setHeader "Content-Type" "text/css"
    file "assets/web/style.css"
  get "/app.js" $ do 
    setHeader "Content-Type" "application/javascript"
    file "assets/web/app.js"
  get "/" $ do
    setHeader "Content-Type" "text/html; charset=utf-8"
    file "assets/web/index.html"
  get "/api/solvers" $ do
    ilist <- liftAndCatchIO $ installedSolvers
    let solverList = SolverList $ map (\s -> SolverStatus (show s) (if s `elem` ilist then "installed" else "not installed")) allSolvers
    json solverList 
  get "/api/transformations" $ do
    json (map show transformationsInOrder)
  get "/api/code/assets" $ do
    -- list assets in ./assets/HighLevel/*.pr
    -- using directory listing
    alist <- liftAndCatchIO $ listDirectoryAssets "assets/HighLevel"
    json $ alist
  get "/api/formulas/assets" $ do
    -- list assets in ./assets/HighLevel/*.pr
    -- using directory listing
    alist <- liftAndCatchIO $ listDirectoryAssets "assets/Formulas"
    json $ alist
  get "/api/code/asset/:name" $ do
    name    <- captureParam "name"
    content <- liftAndCatchIO $ readFile $ "assets/HighLevel/" ++ name
    json $ AssetContent name content
  get "/api/formulas/asset/:name" $ do
    name    <- captureParam "name"
    content <- liftAndCatchIO $ readFile $ "assets/Formulas/" ++ name
    json $ AssetContent name content
  Web.Scotty.post "/api/verify" $ do
    req <- jsonData :: ActionM VerifyRequest
    let hoareTriple = parseVerifyRequest req
    case hoareTriple of
        Left err -> json $ VerifyResponse req err "" []
        Right (ht,simple) -> do
            liftAndCatchIO $ putStrLn $ "Program: transformed to hoare triple" ++ show ht
            solvers <- liftAndCatchIO $ installedSolvers
            liftAndCatchIO $ putStrLn $ "Program: potential solvers " ++ show solvers
            solverResults <- liftAndCatchIO $ mapM (\s -> do
                                                    res <- verifyHoareTriple s ht
                                                    return $ SolverResponse (show s) (show res)) (Mona : solvers)
            liftAndCatchIO $ putStrLn $ "Results: " ++ show solverResults
            json $ VerifyResponse req "" (prettyPrintForProgram simple) solverResults
