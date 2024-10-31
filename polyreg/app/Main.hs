module Main (main) where

import SimpleForPrograms

import Lib

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


main :: IO ()
main = do
    putStrLn . show $ checkEquality "abc"
    putStrLn . show $ checkEquality "a"
    putStrLn . show $ checkEquality "b"
    putStrLn . show $ checkEquality "naruiste nbélopedt bnrest n"
    putStrLn . show $ checkEquality "naruiste nbélopedt bnrest n"
    putStrLn . show $ checkEqualityWithBooleans "ruiste nrest n"
    putStrLn . show $ checkEqualityWithBooleans "naiste  bnrest n"
    putStrLn . show $ checkEqualityWithBooleans "nuiste rest n"
    putStrLn . show $ checkEqualityReverse "abc"
    putStrLn . show $ checkEqualityReverse "a"
    putStrLn . show $ checkEqualityReverse "b"
    putStrLn . show $ checkEqualityReverse "naruiste nbélopedt bnrest n"
