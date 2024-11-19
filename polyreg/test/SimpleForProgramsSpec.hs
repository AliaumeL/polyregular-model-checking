module SimpleForProgramsSpec where

import Test.Hspec

import SimpleForPrograms


data VarP = VarP String deriving(Eq, Show)
data VarB = VarB String deriving(Eq, Show)

-- | example program
-- that prints everything and replaces "a" by "b"s 
--
-- print ’a’ but with normal quotes: 
exampleProgram :: ForProgram VarP VarB Char
exampleProgram = ForProgram []
    [
        For (VarP "i") LeftToRight [] [
            If (LabelAt (VarP "i") 'a') [
                PrintLbl 'b'
            ] [
                PrintPos (VarP "i")
            ]
        ]
    ]

exampleProgramHandCrafted :: String -> String
exampleProgramHandCrafted [] = []
exampleProgramHandCrafted (x:xs) = if x == 'a' then 'b' : exampleProgramHandCrafted xs else x : exampleProgramHandCrafted xs


-- | this program skips the first two letters using booleans
exampleProgramWithBoolans :: ForProgram VarP VarB Char
exampleProgramWithBoolans = ForProgram [VarP "seen1", VarP "seen2"] [
        For (VarP "i") LeftToRight [] [
            If (Not (BoolVar (VarB "seen1"))) 
            [
                SetTrue (VarB "seen1")
            ]
            [
                If (Not (BoolVar (VarB "seen2"))) 
                    [SetTrue (VarB "seen2")]
                    [PrintPos (VarP "i")]
            ]
        ]
    ]

exampleProgramWithBoolansHandCrafted :: String -> String
exampleProgramWithBoolansHandCrafted x = drop 2 x

exampleReverseProgram :: ForProgram VarP VarB Char
exampleReverseProgram = ForProgram [] [
        For (VarP "i") RightToLeft [] [
            PrintPos (VarP "i")
        ]
    ]

exampleReverseProgramHandCrafted :: String -> String
exampleReverseProgramHandCrafted x = reverse x


checkEquality :: String -> Bool
checkEquality s = exampleProgramHandCrafted s == runProgram exampleProgram s

checkEqualityWithBooleans :: String -> Bool
checkEqualityWithBooleans s = exampleProgramWithBoolansHandCrafted s == runProgram exampleProgramWithBoolans s

checkEqualityReverse :: String -> Bool
checkEqualityReverse s = exampleReverseProgramHandCrafted s == runProgram exampleReverseProgram s

spec :: Spec
spec = do
    describe "The interpreter for simple for programs (SimpleForProgram.runProgram)" $ do
        it "runs correctly the a program that swaps 'a' for 'b'" $ do 
            runProgram exampleProgram "abc" `shouldBe` exampleProgramHandCrafted "abc"
            runProgram exampleProgram "a" `shouldBe` exampleProgramHandCrafted "a"
            runProgram exampleProgram "b" `shouldBe` exampleProgramHandCrafted "b"
            runProgram exampleProgram "naruiste nbélopedt bnrest n" `shouldBe` exampleProgramHandCrafted "naruiste nbélopedt bnrest n"
        it "runs correctly a program with boolean variables" $ do
            runProgram exampleProgramWithBoolans "ruiste nrest n" `shouldBe` exampleProgramWithBoolansHandCrafted "ruiste nrest n"
            runProgram exampleProgramWithBoolans "naiste  bnrest n" `shouldBe` exampleProgramWithBoolansHandCrafted "naiste  bnrest n"
            runProgram exampleProgramWithBoolans "nuiste rest n" `shouldBe` exampleProgramWithBoolansHandCrafted "nuiste rest n"
        it "runs correctly a program that reverses a string" $ do
            runProgram exampleReverseProgram "abc" `shouldBe` exampleReverseProgramHandCrafted "abc"
            runProgram exampleReverseProgram "a" `shouldBe` exampleReverseProgramHandCrafted "a"
            runProgram exampleReverseProgram "b" `shouldBe` exampleReverseProgramHandCrafted "b"
            runProgram exampleReverseProgram "naruiste nbélopedt bnrest n" `shouldBe` exampleReverseProgramHandCrafted "naruiste nbélopedt bnrest n"
