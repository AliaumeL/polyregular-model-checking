module FunctionEliminationSpec where

import Test.Hspec

import Data.Map (Map)
import qualified Data.Map as M

import QuantifierFree
import ForPrograms
import ForProgramInterpreter
import Typing.Inference (inferAndCheckProgram)
import ForProgramsTyping
import Parser.ParseHighLevel
import FunctionElimination

fromRight' :: (Show a, Show b) => Either a b -> b
fromRight' (Right x) = x
fromRight' e = error . show $ e


untypeProgram :: Program String a -> Program String ()
untypeProgram = fmap (const ())

spec :: Spec
spec = do 
    describe "The substitution function" $ do
        it "Correctly substitutes a single variable" $ do
            let tc = TOutput TOChar
            let input = (OVar "x" tc)
            let val   = (OConst (CChar 'a' tc) tc)
            let map   = SubstMap { oVars = M.fromList [("x", val)], pVars = M.empty }
            substOExpr map input `shouldBe` val
        it "Correctly substitutes inside statements" $ do
            let tc = TOutput TOChar
            let tl = TOutput (TOList TOChar)
            let tp = TPos (Position (OVar "_" ()))
            let pi = PVar "i" tp
            let pj = PVar "j" tp
            let vx = OVar "x" tc
            let vy = OVar "y" tl
            let ca = CChar 'a' tc
            let cb = CChar 'b' tc
            let cbb = CList [cb, cb] tl
            -- Input : if i < j then x else (yield [x, x])
            let input = (SIf (BComp Le pi pj TBool)
                             (SYield vy tl)
                             (SYield (OList [vx, vx] tl) tl) tl)
            -- substitution x -> 'a' y -> "bb"
            let map = SubstMap { oVars = M.fromList [("x", OConst ca tc),
                                                     ("y", OConst cbb tl)],
                                 pVars = M.empty }
            let expected = (SIf (BComp Le pi pj TBool)
                                (SYield (OConst cbb tl) tl)
                                (SYield (OList [OConst ca tc, OConst ca tc] tl) tl) tl)
            substStmt map input `shouldBe` expected
        it "Works for a slightly complex body" $ do
            let tc = TOutput TOChar
            let tl = TOutput (TOList TOChar)
            let space = CChar ' ' tc
            let seen_space = (BVar "seen_space" TBool)
            let tp = TPos (Position (OVar "_" ()))
            let vs = OVar "s" tc
            let vv = OVar "v" tc
            let map = SubstMap {pVars = M.fromList [], oVars = M.fromList [("s", vs)]}
            let body = SSeq [SLetBoolean "seen_space"
                            (SFor ("i","v",tc) vs 
                                (SSeq [SIf (BOp Conj (BNot seen_space TBool)
                                                    (BNot (BLitEq tc space vv TBool) TBool) TBool)
                                           (SSeq [SYield vv tl] tl)
                                           (SSeq [] tl)
                                           tl]
                                        tl)
                                tl) tl] tl
            substStmt map body `shouldBe` body
    describe "We actually remove function calls in `word_split.pr`" $ do
        testProgram <- runIO $ parseFromFile "assets/word_split.pr"
        let infered = fromRight' (inferAndCheckProgram (fromRight' testProgram))
        it "Starts with a program with function calls" $ do 
            (hasFunctionCall infered) `shouldBe` True
        it "Ends with a program without function calls" $ do
            let eliminated = eliminateFunctionCalls infered
            (hasFunctionCall eliminated) `shouldBe` False
        it "The program still works" $ do
            let eliminated = eliminateFunctionCalls infered
            let input = "go to park"
            let expected = runProgramString (untypeProgram infered)    input
            let actual = runProgramString   (untypeProgram eliminated) input
            actual `shouldBe` expected
    describe "We actually remove function calls in `boolean_funcs.pr`" $ do
        testProgram <- runIO $ parseFromFile "assets/boolean_funcs.pr"
        let infered = fromRight' (inferAndCheckProgram (fromRight' testProgram))
        it "Starts with a program with function calls" $ do 
            (hasFunctionCall infered) `shouldBe` True
        it "Ends with a program without function calls" $ do
            let eliminated = eliminateFunctionCalls infered
            (hasFunctionCall eliminated) `shouldBe` False
        it "The program still works" $ do
            let eliminated = eliminateFunctionCalls infered
            let input = "go to park"
            let expected = runProgramString (untypeProgram infered)    input
            let actual = runProgramString   (untypeProgram eliminated) input
            actual `shouldBe` expected

