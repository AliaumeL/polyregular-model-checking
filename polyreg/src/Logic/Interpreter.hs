module Logic.Interpreter where 

import Logic.Formulas
import Logic.Interpretation

import Data.List (sortBy)

type Tag = String

runInterpretation :: Interpretation Tag -> String -> String
runInterpretation interpretation input =
    let universe = prepareUniverse interpretation input in
    let filteredUniverse = filter (\(tag, ps) -> runDomainFormula (domain interpretation) (tags interpretation) input tag ps) universe in
    let sortedUniverse = sortBy (comparePositions interpretation input) filteredUniverse in
    map (\(tag, ps) -> getPositionLabel interpretation input tag ps) sortedUniverse

generateTuples :: [a] -> Int -> [[a]]  
generateTuples _ 0 = [[]]
generateTuples l n = do 
    x <- l
    xs <- generateTuples l (n-1)
    return (x:xs)

prepareUniverse :: Interpretation Tag -> String -> [(String, [Int])]
prepareUniverse interpretation input = do 
    tag <- tags interpretation
    let ar = arity interpretation tag
    let positions = generateTuples [0..length input - 1] ar
    pos <- positions
    return (tag, pos)

runDomainFormula :: (Tag -> [String] -> Formula String) -> [Tag] -> String -> Tag -> [Int] -> Bool
runDomainFormula formula tags inputWord inputTag inputPs =
    let names = map (\i -> "x" ++ show i) [0..length inputPs - 1] in
    let vars = zip names (PosVal <$> inputPs) in
    evalFormulaWithFreeVars (formula inputTag names) vars tags inputWord

runOrderFormula :: (Tag -> Tag -> [String] -> [String] -> Formula String) -> [Tag] -> String -> Tag -> Tag -> [Int] -> [Int] -> Bool
runOrderFormula formula tags inputWord inputTag1 inputTag2 inputPs1 inputPs2 =
    let names1 = map (\i -> "x" ++ show i) [0..length inputPs1 - 1] in
    let names2 = map (\i -> "y" ++ show i) [0..length inputPs2 - 1] in
    let vars1 = zip names1 (PosVal <$> inputPs1) in
    let vars2 = zip names2 (PosVal <$> inputPs2) in
    evalFormulaWithFreeVars (formula inputTag1 inputTag2 names1 names2) (vars1 ++ vars2) tags inputWord

comparePositions :: Interpretation Tag ->String -> (Tag, [Int]) -> (Tag, [Int]) -> Ordering
comparePositions interpretation word (tag1, ps1) (tag2, ps2) =
    let test = runOrderFormula (order interpretation) (tags interpretation) word tag1 tag2 ps1 ps2 in
    if tag1 == tag2 && ps1 == ps2 then EQ
    else if test then LT
    else GT

getPositionLabel :: Interpretation Tag -> String -> Tag -> [Int] -> Char
getPositionLabel interpretation word tag ps =
    case labelOrCopy interpretation tag of
        Left c -> c
        Right i -> word !! (ps !! i)

