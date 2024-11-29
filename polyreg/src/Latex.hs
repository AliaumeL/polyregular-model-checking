module Latex where

class ToLatex a where
  toLatex :: a -> String

printLatex :: ToLatex a => a -> IO ()
printLatex = putStrLn . toLatex


