module SmtSolver where

import TwoSortedFormulas (Formula)

data SmtResult = Sat | Unsat | Unknown
  deriving (Show, Eq)

class SmtSolver a where
    smtAssert    :: a -> Formula String String -> a
    smtExtension :: a -> String
    smtCheckSat  :: a -> Formula String String -> IO (SmtResult, String)

data MonaSolver = MonaSolver {
    monaPath :: String
}

instance SmtSolver MonaSolver where
    smtAssert solver formula = solver
    smtExtension solver = "mona"
    smtCheckSat solver formula = return (Unknown, "Not implemented")

