{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.FormulaChecker (TypeError(..), checkFormulaTypes) where

import Logic.Formulas
import Control.Monad.Reader
import Control.Monad.Except
import Data.Map (Map)
import qualified Data.Map as M

data TypeError = TypeMismatch     Var Sort Sort (Formula ()) (Formula ())
               | IndexOutOfBounds Var Int
               | IndexWrongType   Var Int Sort Sort
    deriving (Show,Eq)

newtype TypeStack = TypeStack { quantifierStack :: [Sort] } deriving(Eq, Show)

newtype TypeCheckMonad a = TypeCheckMonad { runTypeCheckMonad :: ReaderT TypeStack (Either TypeError) a }
    deriving (Functor, Applicative, Monad, MonadReader TypeStack, MonadError TypeError)

-- Function to check if a formula is well-typed
checkFormulaTypes :: Formula tag -> Either TypeError (Map Var Sort)
checkFormulaTypes formula = runReaderT (runTypeCheckMonad $ check formula) (TypeStack [])


checkLocalType :: Int -> String -> Sort -> TypeCheckMonad ()
checkLocalType i x s = do
  stack <- asks quantifierStack
  if i >= length stack then 
    throwError $ IndexOutOfBounds (Local i x) (length stack)
  else 
    let s' = stack !! i in
    if not (s' == s) then 
        throwError $ IndexWrongType (Local i x) i s (stack !! i)
    else return ()

checkVar :: Var -> Sort -> TypeCheckMonad (Map Var Sort)
checkVar (In x) s      = return $ M.singleton (In x) s
checkVar (Out x) s     = return $ M.singleton (Out x) s
checkVar (Local i x) s = checkLocalType i x s >> return M.empty


-- Helper function to check types recursively
check :: Formula tag -> TypeCheckMonad (Map Var Sort)
check (FConst _)         = return M.empty
check (FVar v)           = checkVar v Boolean
check (FTag v _)         = checkVar v Tag
check (FLetter v _)      = checkVar v Pos
check (FRealPos v)       = checkVar v Pos
check f@(FTestPos _ v1 v2) = do
  varTypes1 <- checkVar v1 Pos
  varTypes2 <- checkVar v2 Pos
  unionWithCheck varTypes1 (ignoreTags f) varTypes2 (ignoreTags f)
check (FBin _ l r) = do
  leftTypes  <- check l
  rightTypes <- check r
  unionWithCheck leftTypes (ignoreTags l) rightTypes (ignoreTags r)
check (FNot f)              = check f
check (FQuant _ _ s f)      = local (\(TypeStack qs) ->  TypeStack (s:qs)) $ check f

unionWithCheck :: Map Var Sort -> Formula () -> Map Var Sort -> Formula () -> TypeCheckMonad (Map Var Sort)
unionWithCheck m1 f1 m2 f2 = M.traverseWithKey checkConsistency m1 >>= \m1' ->
                       M.traverseWithKey checkConsistency m2 >>= \m2' ->
                       return (M.union m1' m2')
  where
    checkConsistency :: Var -> Sort -> TypeCheckMonad Sort
    checkConsistency var sort = case M.lookup var m2 of
      Just sort2 
        | sort == sort2 -> return sort
        | otherwise -> throwError $ TypeMismatch var sort sort2 f1 f2
      Nothing -> return sort
