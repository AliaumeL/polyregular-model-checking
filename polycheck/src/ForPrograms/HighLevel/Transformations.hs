module ForPrograms.HighLevel.Transformations
(
    Transformation(..)
  , transformationsInOrder
  , applyTransform
  , safeApplyTransform
)
where

import ForPrograms.HighLevel 
import ForPrograms.HighLevel.Typing (eraseTypesInFunctions)

-- Import the transformations
import ForPrograms.HighLevel.Transformations.BooleanElimination (removeBooleanGen)
import ForPrograms.HighLevel.Transformations.LetBoolsToTop (bringLetBoolsToTopAndRefresh)
import ForPrograms.HighLevel.Transformations.FunctionElimination (eliminateFunctionCalls)
import ForPrograms.HighLevel.Transformations.LiteralElimination (eliminateLiterals)
import ForPrograms.HighLevel.Transformations.LetElimination (eliminateLetProgram)
import ForPrograms.HighLevel.Transformations.ForLoopExpansion (forLoopExpansion, forLoopExpansionFix)
import ForPrograms.HighLevel.Transformations.ReturnElimination (retElimProgram)
import ForPrograms.HighLevel.Transformations.ReductionLitEq (removeBLitEq)
import ForPrograms.HighLevel.Transformations.EvaluateConstantEqualities (removeConstantEquality)

-- Typecheck the program 
import ForPrograms.HighLevel.Typing(ValueType(..))
import ForPrograms.HighLevel.Typing.Inference (inferAndCheckProgram)

data Transformation = LitEqElimination
                    | FunctionElimination
                    | LiteralElimination    
                    | BooleanElimination
                    | LetOutputElimination
                    | ReturnElimination
                    | ForLoopExpansion
                    | LetBoolsToTop
                    | ConstEqEval
                    deriving (Eq,Show,Read,Ord,Enum)

transformationsInOrder :: [Transformation]
transformationsInOrder = [LitEqElimination .. ConstEqEval]

applyTransform :: Transformation -> Program String ValueType -> Program String ValueType
applyTransform ConstEqEval p = removeConstantEquality p
applyTransform BooleanElimination p = removeBooleanGen p
applyTransform FunctionElimination p = eliminateFunctionCalls p
applyTransform LiteralElimination p = eliminateLiterals p
applyTransform LitEqElimination p = removeBLitEq p
applyTransform LetOutputElimination p = eliminateLetProgram p
applyTransform ReturnElimination p = retElimProgram p
applyTransform ForLoopExpansion p = case forLoopExpansionFix p of  
    Left err -> error $ "Error in for loop expansion: " ++ show err
    Right p' -> p'
applyTransform LetBoolsToTop p = bringLetBoolsToTopAndRefresh p

checkIfStillValid :: Program String ValueType -> Either String (Program String ValueType)
checkIfStillValid p = case inferAndCheckProgram erasedTypes of
                        Left err -> Left $ "Error after transformation: " ++ show err
                        Right p' -> Right p'
    where
        erasedTypes = eraseTypesInFunctions p

safeApplyTransform :: Transformation -> Program String ValueType -> Either String (Program String ValueType)
safeApplyTransform t p = do
    let p' = applyTransform t p
    checkIfStillValid p'
