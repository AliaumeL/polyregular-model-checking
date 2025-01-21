module Logic.HoareTriple
(
   HoareTriple(..)
 , verifyHoareTriple
 , encodeHoareTriple
)
where

import Logic.Formulas
import QuantifierFree

import Logic.Interpretation
import Logic.PullBack
import Logic.Export

import Data.List (nub)

data HoareTriple = HoareTriple {
  pre     :: Formula (),
  program :: Interpretation String,
  post    :: Formula ()
} deriving (Show)


encodeHoareTriple :: HoareTriple -> Formula String
encodeHoareTriple (HoareTriple pre program post) = FBin Impl (addRealPositions (injectTags pre)) (pullBack program post)

verifyHoareTriple :: PossibleSolvers -> HoareTriple -> IO ExportResult
verifyHoareTriple solver t = encodeAndRun solver params triple
    where
        i         = program t
        tripleRaw = encodeHoareTriple t
        triple    = simplifyFormula $ FNot tripleRaw
        params    = EncodeParams (nub $ "abcd" ++ Logic.Interpretation.alphabet i) (Logic.Interpretation.tags i)
