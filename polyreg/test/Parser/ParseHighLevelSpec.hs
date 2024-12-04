module Parser.ParseHighLevelSpec where

import Test.Hspec
import Parser.ParseHighLevel
import Data.Either

testProgram :: String
testProgram = unlines [
  "def getFirstWord (s : [Char]) : [Char] :=",
  "    let mut seen_space : Bool := False in",
  "    for (i, v) in s do ",
  "        if not seen_space and v !== ' ' then ",
  "            yield v",
  "        endif",
  "        if v === ' ' then ",
  "            setTrue seen_space",
  "        endif",
  "    done",
  "def getCurrentWord (s : [Char] with (i)) : [Char] :=",
  "    let mut seen_space : Bool := False in",
  "    for (j, v) in s do ",
  "       if j > i then ",
  "           if v === ' ' then ",
  "               setTrue seen_space",
  "           endif",
  "           if not seen_space then ",
  "              yield v ",
  "           endif",
  "       endif",
  "     done ",
  "def words (s : [Char]) : [[Char]] :=",
  "    yield getFistWord(s) ",
  "    for (i, v) in s do ",
  "        if v === ' ' then ",
  "            yield getCurrentWord(s with (i)) ",
  "        else ",
  "            yield v",
  "        endif ",
  "     done"
  ]

spec :: Spec
spec = 
    describe "The parser should be able to parse programs" $ do 
        it "Parses a simple program" $ do
            let parsed = parseHighLevel testProgram
            parsed `shouldSatisfy` isRight