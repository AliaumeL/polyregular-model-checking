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


data PossibleSolvers = Mona | AltErgoSingle | SMTLib SMTLibSolver deriving (Eq,Show,Ord,Read)
    
allSolvers :: [PossibleSolvers]
allSolvers = [Mona, SMTLib Z3, SMTLib CVC5, SMTLib Yices, SMTLib AltErgo]


solverIsInstalled :: PossibleSolvers -> IO Bool
solverIsInstalled Mona             = processIsInstalled "mona"
solverIsInstalled AltErgoSingle    = processIsInstalled "alt-ergo"
solverIsInstalled (SMTLib Z3)      = processIsInstalled "z3"
solverIsInstalled (SMTLib CVC5)    = processIsInstalled "cvc5"
solverIsInstalled (SMTLib Yices)   = processIsInstalled "yices"
solverIsInstalled (SMTLib AltErgo) = processIsInstalled "alt-ergo"

writeToDebugFile :: PossibleSolvers -> String -> IO String
writeToDebugFile Mona s          = writeFile "tmp.mona" s >> return s
writeToDebugFile AltErgoSingle s = writeFile "tmp.ae" s   >> return s
writeToDebugFile (SMTLib x) s    = writeFile ("tmp." ++ computeExt x) s >> return s
    where
        computeExt Z3 = "z3.smt2"
        computeExt CVC5 = "cvc5.smt2"
        computeExt Yices = "yices.smt2"
        computeExt AltErgo = "ae.smt2"


encoder :: PossibleSolvers -> EncodeParams -> Formula String -> String
encoder Mona p          = encodeMona    p
encoder AltErgoSingle p = encodeAltErgo p
encoder (SMTLib _) p    = encodeSMTLib  p

runner :: PossibleSolvers -> String -> IO ExportResult
runner Mona p          = runMona     p
runner AltErgoSingle p = runAltErgo  p
runner (SMTLib s) p    = runSMTLib s p


installedSolvers :: IO [PossibleSolvers]
installedSolvers = filterM solverIsInstalled allSolvers

encodeAndRun :: PossibleSolvers -> EncodeParams -> Formula String -> IO ExportResult
encodeAndRun ps p s = do
    let encoded = encoder ps p s
    writeToDebugFile ps encoded
    runner ps encoded
