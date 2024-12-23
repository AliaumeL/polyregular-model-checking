{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Interpretation where

import Logic.Formulas
import QuantifierFree


data Interpretation tag = Interpretation {
    tags       :: [tag],
    inputAlph  :: String,
    outputAlph :: String,
    domain     :: tag -> [String] -> Formula tag,
    order      :: tag -> tag  -> [String] -> [String] -> Formula tag,
    label      :: tag -> Char -> [String] -> Formula tag,
    copy       :: tag -> Char -> [String] -> Formula tag,
    arity      :: tag -> Int,
    maxArity   :: Int
}

-- TODO: evalInterpretation
