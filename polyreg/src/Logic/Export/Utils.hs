{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Export.Utils where

import Logic.QuantifierFree

import Control.Monad
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as M

import System.Process (readProcessWithExitCode)
import GHC.IO.Exception
import Control.Exception (catch)

import Data.Char

import Logic.Formulas

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (x:xs) = x : sep : intersperse sep xs

class (Monad m) => MonadExport m where
    withVariable  :: Sort -> m a -> m a
    getVarName    :: Int -> m String

data ExportState = ExportState { 
    varStack :: [String],
    nextVar :: Int 
} deriving(Eq, Show)

newtype ExportM a = ExportM (State ExportState a) 
    deriving(Monad,Applicative,Functor, MonadState ExportState)

instance MonadExport ExportM where
    withVariable s (ExportM m) = do
        count <- gets nextVar
        stack <- gets varStack
        let newVar = take 1 (show s) ++ show count
        modify (\(ExportState m n) -> ExportState (newVar : m) (n+1))
        res <- ExportM m
        modify (\(ExportState m n) -> ExportState stack n)
        return res
    getVarName i = do
        stack <- gets varStack
        return $ stack !! i

runExportM :: ExportM a -> a
runExportM (ExportM m) = evalState m (ExportState [] 0)

safeEncodeLetter :: Char -> String
safeEncodeLetter c = if isAlpha c then [c] else show (ord c)

data EncodeParams = EncodeParams {
    alphabet :: String,
    tags     :: [String]
} deriving (Eq,Show)


data ExportResult = Sat | Unsat | Unknown | Error String
  deriving (Show, Eq)

safeRunProcess :: String -> [String] -> IO (Either String String)
safeRunProcess p args = catch callCommand handler
    where
        handler e = return $ Left $ show (e :: IOException)
        callCommand = do 
            (exitCode, stdout, stderr) <- readProcessWithExitCode p args ""
            case exitCode of
                ExitSuccess   -> return $ Right stdout
                ExitFailure i -> return $ Left $ (show  i) ++ " : " ++ stderr


processIsInstalled :: String -> IO Bool
processIsInstalled p = do
    res <- safeRunProcess p ["--version"]
    case res of
        Left _  -> return False
        Right _ -> return True