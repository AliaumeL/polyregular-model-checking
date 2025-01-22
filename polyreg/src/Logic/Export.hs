module Logic.Export 
(
   ExportResult(..)
 , EncodeParams(..)
 , SMTLibSolver(..)
 , PossibleSolvers(..)
 , allSolvers
 , solverIsInstalled
 , installedSolvers
 , encodeAndRun
)
where

import Logic.Formulas
import Logic.Export.Utils
import Logic.Export.Mona
import Logic.Export.SMTLib
import Logic.Export.AltErgo
import Control.Monad (filterM)


data PossibleSolvers = Mona | AltErgoSingle | SMTLib SMTLibSolver deriving (Eq,Show,Ord)
    
allSolvers :: [PossibleSolvers]
allSolvers = [Mona, AltErgoSingle, SMTLib Z3, SMTLib CVC5, SMTLib Yices, SMTLib AltErgo]


solverIsInstalled :: PossibleSolvers -> IO Bool
solverIsInstalled Mona             = processIsInstalled "mona"
solverIsInstalled AltErgoSingle    = processIsInstalled "alt-ergo"
solverIsInstalled (SMTLib Z3)      = processIsInstalled "z3"
solverIsInstalled (SMTLib CVC5)    = processIsInstalled "cvc5"
solverIsInstalled (SMTLib Yices)   = processIsInstalled "yices"
solverIsInstalled (SMTLib AltErgo) = processIsInstalled "alt-ergo"

installedSolvers :: IO [PossibleSolvers]
installedSolvers = filterM solverIsInstalled allSolvers

encodeAndRun :: PossibleSolvers -> EncodeParams -> Formula String -> IO ExportResult
encodeAndRun Mona p           = runMona     . encodeMona p
encodeAndRun AltErgoSingle p  = runAltErgo  . encodeAltErgo p
encodeAndRun (SMTLib s) p     = runSMTLib s . encodeSMTLib p
