{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ForPrograms.HighLevel.Typing where

import ForPrograms.HighLevel

import Data.Map    (Map)
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (forM)

import Data.Tuple.Extra

-------
-- As a first step, we need to go from typed AST to untyped AST.
-- This is needed because the type of a *position* is the
-- *origin* of this position in terms of *untyped AST*.
-------

eraseTypesO :: OExpr v t -> OExpr v ()
eraseTypesO p = fmap (const ()) p

data OutputType = TOList OutputType
                | TOChar
                deriving (Show, Eq, Ord)

outputTypeDepth :: OutputType -> Int
outputTypeDepth TOChar = 0
outputTypeDepth (TOList t) = 1 + outputTypeDepth t

depthToType :: Int -> OutputType
depthToType n | n < 0 = error "Invalid depth"
depthToType 0 = TOChar
depthToType n = TOList $ depthToType (n-1)

data Position = Position (OExpr String ())
    deriving (Show, Eq, Ord)

unPosition :: Position -> OExpr String ()
unPosition (Position o) = o

data Argument = Argument OutputType Int 
    deriving (Show, Eq, Ord)

data FunctionType = FProd [Argument] ValueType
    deriving (Show, Eq, Ord)

data ValueType = TBool
               | TPos Position 
               | TOutput OutputType
    deriving (Show, Eq, Ord)


type TProgram = Program String ValueType

class HasType a where
    getType :: a -> ValueType

instance HasType (Stmt String ValueType) where
    getType (SIf _ _ _ t) = t
    getType (SYield _ t) = t
    getType (SOReturn _ t) = t
    getType (SBReturn _ t) = t
    getType (SLetOutput _ _ _ t) = t
    getType (SLetBoolean _ _ t) = t
    getType (SSetTrue _ t) = t
    getType (SFor _ _ _ _ t) = t
    getType (SSeq _ t) = t

instance HasType (BExpr String ValueType) where
    getType (BConst _ t) = t
    getType (BNot _ t) = t
    getType (BOp _ _ _ t) = t
    getType (BComp _ _ _ t) = t
    getType (BVar _ t) = t
    getType (BGen _ t) = t
    getType (BApp _ _ t) = t
    getType (BLitEq _ _ _ t) = t

instance HasType (PExpr String ValueType) where
    getType (PVar _ t) = t

instance HasType (CExpr String ValueType) where
    getType (CChar _ t) = t
    getType (CList _ t) = t

instance HasType (OExpr String ValueType) where
    getType (OVar _ t) = t
    getType (OConst _ t) = t
    getType (OList _ t) = t
    getType (OApp _ _ t) = t
    getType (OGen _ t) = t

instance HasType (StmtFun String ValueType) where
    getType (StmtFun _ _ _ t) = t
