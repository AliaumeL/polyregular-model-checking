module SimpleForProgramsSpec where

import Test.Hspec

import SimpleForPrograms

-- | example program
-- that prints everything and replaces "a" by "b"s 
--
-- print ’a’ but with normal quotes: 
exampleProgram :: ForProgram
exampleProgram = ForProgram []
    [
        For (PName "i") LeftToRight [] (
            If (BLabelAt (PName "i") 'a') (
                PrintLbl 'b'
            ) (
                PrintPos (PName "i")
            )
        )
    ]

exampleProgramHandCrafted :: String -> String
exampleProgramHandCrafted [] = []
exampleProgramHandCrafted (x:xs) = if x == 'a' then 'b' : exampleProgramHandCrafted xs else x : exampleProgramHandCrafted xs


-- | this program skips the first two letters using booleans
exampleProgramWithBoolans :: ForProgram
exampleProgramWithBoolans = ForProgram [BName "seen1", BName "seen2"] [
        For (PName "i") LeftToRight [] (
            If (BNot (BVar (BName "seen1"))) 
            (
                SetTrue (BName "seen1")
            )
            (
                If (BNot (BVar (BName "seen2"))) 
                    (SetTrue  (BName "seen2"))
                    (PrintPos (PName "i"))
            )
        )
    ]

exampleProgramWithBoolansHandCrafted :: String -> String
exampleProgramWithBoolansHandCrafted x = drop 2 x

exampleReverseProgram :: ForProgram
exampleReverseProgram = ForProgram []
        For (PName "i") RightToLeft [] (Seq [
            PrintPos (PName "i")
        ])

exampleReverseProgramHandCrafted :: String -> String
exampleReverseProgramHandCrafted x = reverse x


checkEquality :: String -> Bool
checkEquality s = (Right $ exampleProgramHandCrafted s) == runProgram exampleProgram s

checkEqualityWithBooleans :: String -> Bool
checkEqualityWithBooleans s = (Right $ exampleProgramWithBoolansHandCrafted s) == runProgram exampleProgramWithBoolans s

checkEqualityReverse :: String -> Bool
checkEqualityReverse s = (Right $ exampleReverseProgramHandCrafted s) == runProgram exampleReverseProgram s

spec :: Spec
spec = do
    describe "The interpreter for simple for programs (SimpleForProgram.runProgram)" $ do
        it "runs correctly the a program that swaps 'a' for 'b'" $ do 
            runProgram exampleProgram "abc" `shouldBe` (Right $ exampleProgramHandCrafted "abc")
            runProgram exampleProgram "a" `shouldBe` (Right $ exampleProgramHandCrafted "a")
            runProgram exampleProgram "b" `shouldBe` (Right $ exampleProgramHandCrafted "b")
            runProgram exampleProgram "naruiste nbélopedt bnrest n" `shouldBe` (Right $ exampleProgramHandCrafted "naruiste nbélopedt bnrest n")
        it "runs correctly a program with boolean variables" $ do
            runProgram exampleProgramWithBoolans "ruiste nrest n" `shouldBe` (Right $ exampleProgramWithBoolansHandCrafted "ruiste nrest n")
            runProgram exampleProgramWithBoolans "naiste  bnrest n" `shouldBe` (Right $ exampleProgramWithBoolansHandCrafted "naiste  bnrest n")
            runProgram exampleProgramWithBoolans "nuiste rest n" `shouldBe` (Right $ exampleProgramWithBoolansHandCrafted "nuiste rest n")
        it "runs correctly a program that reverses a string" $ do
            runProgram exampleReverseProgram "abc" `shouldBe` (Right $ exampleReverseProgramHandCrafted "abc")
            runProgram exampleReverseProgram "a" `shouldBe` (Right $ exampleReverseProgramHandCrafted "a")
            runProgram exampleReverseProgram "b" `shouldBe` (Right $ exampleReverseProgramHandCrafted "b")
            runProgram exampleReverseProgram "naruiste nbélopedt bnrest n" `shouldBe` (Right $ exampleReverseProgramHandCrafted "naruiste nbélopedt bnrest n")
