{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Typing.Constraints where


import qualified Data.Map as M

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

import qualified Data.Graph as G

import Data.Foldable (toList)

data Type  = TBool | TList Int deriving (Eq, Ord, Show)
data Label = Var Int | Const Type deriving (Eq, Ord, Show)
data Constraint = Equal | Plus | Minus deriving (Eq, Ord, Show)

updateType :: Constraint -> Type -> Maybe Type
updateType Equal t = Just t
updateType Plus (TList n) = Just $ TList (n+1)
updateType Minus (TList n) = Just $ TList (n-1)
updateType _ _ = Nothing

data ConstraintGraph = ConstraintGraph {
    graph :: G.Graph,  -- the graph of constraints
    const :: IntMap.IntMap Type,
    elbl  :: M.Map (Int, Int) Constraint -- edge labels
} deriving (Show, Eq)


-- | Create a constraint graph from a list of constraints
-- of the form "[x] = y" ; "x = y" or "x = Type"

data GraphSpec = VarConstraint (Int, Constraint, Int)
               | VarType (Int, Type)
               deriving (Show, Eq)

createGraph :: [GraphSpec] -> ConstraintGraph
createGraph specs = ConstraintGraph g const elbl
    where
        nodeMax     = maximum [max x y | VarConstraint (x, _, y) <- specs]
        constVals   = IntSet.fromList [x | VarType (_, (TList x)) <- specs]
        boolNode    = nodeMax + 1
        constNodes  = IntMap.fromList $ zip (IntSet.toList constVals) [nodeMax+2..]
        numberNodes = nodeMax + 1 + IntMap.size constNodes

        cstrToLbl (VarConstraint (x, c, y)) = ((x, y), c)
        cstrToLbl (VarType (x, TBool))      = ((x, boolNode), Equal)
        cstrToLbl (VarType (x, (TList y)))  = case IntMap.lookup y constNodes of
            Just n  -> ((x, n), Equal)
            Nothing -> error "Invalid type"
        elbl       = M.fromList . concatMap (undirected . cstrToLbl) $ specs
        g          = G.buildG (0, numberNodes) $ M.keys elbl
        const = IntMap.fromList $ (boolNode, TBool) : [(y, TList x) | (x, y) <- IntMap.toList constNodes]

        undirected :: ((Int, Int), Constraint) -> [((Int, Int), Constraint)]
        undirected ((x, y), Equal) = [((x, y), Equal), ((y, x), Equal)]
        undirected ((x, y), Plus) = [((x, y), Plus), ((y, x), Minus)]
        undirected ((x, y), Minus) = [((x, y), Minus), ((y, x), Plus)]


-- | Solve the constraints! 
-- To do this, it suffices to
-- 1. compute a spanning forest of the graph rooted at the 
--    boolean node / constant nodes
-- 2. check that all nodes are covered by the forest
-- 3. propagate types from the roots of the forests to their leaves


propagateTreeNode :: M.Map (Int,Int) Constraint -> Int -> Type -> G.Tree Int -> [(Int, Type)]
propagateTreeNode elbl source tsource (G.Node x ts) = (x, tx) : concatMap (propagateTreeNode elbl x tx) ts
    where
        tx = case M.lookup (source, x) elbl of
            Just c  -> case updateType c tsource of
                Just t  -> t
                Nothing -> error $ "Invalid constraint " ++ show source ++ " : " ++ show c ++ " " ++ show tsource ++ " " ++ show x
            Nothing -> error "Unreachable node"

data SolverError = UncoveredNodes [IntSet.IntSet] deriving (Show)

solveConstraints :: ConstraintGraph -> Either SolverError (IntMap.IntMap Type) 
solveConstraints (ConstraintGraph g c elbl) = if IntSet.null uncoveredNodes then
                                                  Left (UncoveredNodes err)
                                              else
                                                  Right (IntMap.fromList $ propagateAllTrees)
    where
        forest :: G.Forest Int
        forest = G.dfs g $ IntMap.keys c

        propagateTree :: G.Tree Int -> [(Int, Type)]
        propagateTree (G.Node x xs) = case IntMap.lookup x c of
            Just t  -> concatMap (propagateTreeNode elbl x t) xs
            Nothing -> error "Invalid node"

        propagateAllTrees :: [(Int, Type)]
        propagateAllTrees = concatMap propagateTree forest

        uncoveredNodes :: IntSet.IntSet
        uncoveredNodes = IntSet.difference allNodes $ IntSet.fromList $ map fst propagateAllTrees
            where
                allNodes = IntSet.fromList $ G.vertices g

        errTrees :: G.Forest Int
        errTrees = G.dfs g $ IntSet.toList uncoveredNodes

        err :: [IntSet.IntSet]
        err = map (IntSet.fromList . toList) errTrees


