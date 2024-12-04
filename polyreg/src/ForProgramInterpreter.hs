module ForProgramInterpreter where

import Control.Monad.State 
import qualified Data.Map as M
import Data.Tuple.Extra

import ForPrograms 

data InterpreterState = InterpreterState {
    vDict :: M.Map String (CExpr String ()),
    posDict :: M.Map String Int,
    bools :: M.Map String Bool ,
    functions :: M.Map String (StmtFun String ()) 
}

emptyInterpreterState :: [StmtFun String ()] -> InterpreterState
emptyInterpreterState fs = InterpreterState {
    vDict = M.empty,
    posDict = M.empty,
    bools = M.empty,
    functions = M.fromList $ map (\f -> (funName f, f)) fs
}

type InterpreterMonad = State InterpreterState

data Value = VBool Bool | VOutput (CExpr String ())

interpretFunction :: StmtFun String () -> [(CExpr String (), [Int])] -> InterpreterMonad Value 
interpretFunction (StmtFun _ args stmt _) args' = do
    let argsO = M.fromList $ zip (map fst3 args) (map fst args')
    let argsP = M.fromList $ zip (concatMap thd3 args) (concatMap snd args')
    currentState <- get
    let newState = currentState {
        vDict = M.union (vDict currentState) argsO,
        posDict = M.union (posDict currentState) argsP
    }
    put newState
    ans <- interpretStmt stmt
    put currentState
    return ans

interpretStmt :: Stmt String () -> InterpreterMonad Value
interpretStmt = undefined 

interpretBExpr :: BExpr String () -> InterpreterMonad Bool
interpretBExpr = undefined

interpretOExpr :: OExpr String () -> InterpreterMonad (CExpr String ())
interpretOExpr = undefined

