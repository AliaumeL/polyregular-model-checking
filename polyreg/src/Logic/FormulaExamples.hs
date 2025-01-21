module Logic.FormulaExamples where

import Logic.QuantifierFree
import Logic.Formulas

containsAB :: Char -> Char -> Formula ()
containsAB c1 c2 = quantifyList [("firstC", Pos, Exists), ("nextC", Pos, Exists)] $ andList [iLessThanJ, consecutive, iIsC, jIsC]
    where
        iLessThanJ = FTestPos Lt (Local 1 "firstC") (Local 0 "nextC")
        consecutive = FNot . quantifyList [("middleLetter", Pos, Exists)] . andList $ [
            FTestPos Lt (Local 2 "firstC") (Local 0 "middleLetter"),
            FTestPos Lt (Local 0 "middleLetter") (Local 1 "nextC") ]
        iIsC       = FLetter (Local 1 "firstC") c1
        jIsC       = FLetter (Local 0 "nextC")  c2

startsWithChar :: Char -> Formula ()
startsWithChar c = quantifyList [("firstC", Pos, Exists)] $ andList [iIsC, isFirst]
    where
        iIsC       = FLetter (Local 0 "firstC") c
        isFirst    = FNot $ quantifyList [("beforeFirst", Pos, Exists)] $ FTestPos Lt (Local 0 "beforeFirst") (Local 1 "firstC")

endsWithChar :: Char -> Formula ()
endsWithChar c = quantifyList [("lastC", Pos, Exists)] $ andList [jIsC, isLast]
    where
        jIsC       = FLetter (Local 0 "lastC") c
        isLast     = FNot $ quantifyList [("afterLast", Pos, Exists)] $ FTestPos Lt (Local 1 "lastC") (Local 0 "afterLast")
