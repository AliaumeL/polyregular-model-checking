{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Typing.Constraints where

import qualified ForPrograms as FP
import qualified Data.Map as M
import qualified Data.Set    as S

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

import qualified Data.Array as A
import qualified Data.Graph as G

import Control.Monad
import Control.Monad.State

import Data.Foldable (toList)


data Type       = TBool | TList Int | TPos (FP.OExpr String ()) deriving (Eq, Ord, Show)
data Constraint = Equal | Plus | Minus deriving (Eq, Ord, Show)

updateType :: Constraint -> Type -> Maybe Type
updateType Equal t = Just t
updateType Minus (TList n) = Just $ TList (n+1)
updateType Plus (TList n) = Just $ TList (n-1)
updateType _ _ = Nothing

data ConstraintGraph = ConstraintGraph {
    graph :: G.Graph,                    -- the graph of constraints
    csts  :: IntMap.IntMap Type,         -- "sink" / "constant" nodes
    elbl  :: M.Map (Int, Int) Constraint -- edge labels
} deriving (Show, Eq)


data GraphSpec = VarConstraint (Int, Constraint, Int)
               | VarType (Int, Type)
               deriving (Show, Eq)

createGraph :: [GraphSpec] -> ConstraintGraph
createGraph specs = ConstraintGraph g const elbl
    where
        nodeMax     = maximum [max x y | VarConstraint (x, _, y) <- specs]
        constTypes  = S.fromList [t | VarType (_, t) <- specs]

        constNodes :: M.Map Type G.Vertex
        constNodes = M.fromList $ zip (S.toList constTypes) [nodeMax+1..]

        numberNodes :: Int
        numberNodes = nodeMax + M.size constNodes

        cstrToLbl :: GraphSpec -> ((G.Vertex, G.Vertex), Constraint)
        cstrToLbl (VarConstraint (x, c, y)) = ((x, y), c)
        cstrToLbl (VarType (x, t))          = case M.lookup t constNodes of
            Just n  -> ((x, n), Equal)
            Nothing -> error "Invalid type"

        elbl :: M.Map (Int, Int) Constraint
        elbl       = M.fromList . concatMap (undirected . cstrToLbl) $ specs
        g          = G.buildG (0, numberNodes) $ M.keys elbl

        const :: IntMap.IntMap Type
        const = IntMap.fromList $ map (\(t,n) -> (n, t)) $ M.toList constNodes

        undirected :: ((Int, Int), Constraint) -> [((Int, Int), Constraint)]
        undirected ((x, y), Equal) = [((x, y), Equal), ((y, x), Equal)]
        undirected ((x, y), Plus)  = [((x, y), Plus),  ((y, x), Minus)]
        undirected ((x, y), Minus) = [((x, y), Minus), ((y, x), Plus)]


-- | Solve the constraints! 
-- To do this, it suffices to
-- 1. compute a spanning forest of the graph rooted at the 
--    boolean node / constant nodes
-- 2. check that all nodes are covered by the forest
-- 3. propagate types from the roots of the forests to their leaves

data SolverError = UncoveredNodes [IntSet.IntSet]                 -- Some nodes cannot be inferred
                 | InvalidConstraint Int Int Constraint Type      -- The inference failed 
                 | InconsistentGraph Int Int Constraint Type Type -- There is a type inconsistency in the resulting graph
    deriving (Show)

propagateTreeNode :: M.Map (Int,Int) Constraint -> Int -> Type -> G.Tree Int -> Either SolverError [(Int, Type)]
propagateTreeNode elbl source tsource (G.Node x ts) = do
                                                        rtx <- tx 
                                                        rst <- mapM (propagateTreeNode elbl x rtx) ts
                                                        return $ (x, rtx) : concat rst
    where
        tx = case M.lookup (source, x) elbl of
            Just c  -> case updateType c tsource of
                Just t  -> Right t
                Nothing -> Left $ InvalidConstraint source x c tsource
            Nothing -> error "Unreachable node"
    

solveConstraints :: ConstraintGraph -> Either SolverError (IntMap.IntMap Type) 
solveConstraints (ConstraintGraph g c elbl) = do
                                                allTrees <- propagateAllTrees
                                                uncov    <- uncoveredNodes
                                                error    <- err
                                                case IntSet.null uncov of
                                                    True  -> return $ IntMap.fromList (IntMap.toList c ++ allTrees)
                                                    False -> Left $ UncoveredNodes error
    where
        forest :: G.Forest Int
        forest = G.dfs g $ IntMap.keys c

        propagateTree :: G.Tree Int -> Either SolverError [(Int, Type)]
        propagateTree (G.Node x xs) = case IntMap.lookup x c of
            Just t  -> concat <$> mapM (propagateTreeNode elbl x t) xs
            Nothing -> error "Invalid node"

        propagateAllTrees :: Either SolverError [(Int, Type)]
        propagateAllTrees = concat <$> mapM propagateTree forest

        uncoveredNodes :: Either SolverError IntSet.IntSet
        uncoveredNodes = do
                            let allNodes   = IntSet.fromList $ G.vertices g
                            let allTouched = IntSet.fromList . concatMap (toList) $ forest
                            return $ IntSet.difference allNodes allTouched

        errTrees :: Either SolverError (G.Forest Int)
        errTrees = do 
                    nodes <- uncoveredNodes
                    return $ G.dfs g (IntSet.toList nodes)

        err :: Either SolverError [IntSet.IntSet]
        err = map (IntSet.fromList . toList) <$> errTrees



aggregateErrors :: [Either SolverError a] -> Either [SolverError] ()
aggregateErrors [] = Right ()
aggregateErrors (Right _ : xs) = aggregateErrors xs
aggregateErrors (Left x : xs) = case aggregateErrors xs of
    Right () -> Left [x]
    Left xs -> Left (x:xs)

-- Verifies that all edges in the constraint graph are 
-- satisfied.
verifyConstraints :: IntMap.IntMap Type -> ConstraintGraph -> Either [SolverError] ()
verifyConstraints types (ConstraintGraph _ _ elbl) = aggregateErrors $ map verifyEdge $ M.toList elbl
    where
        verifyEdge :: ((Int, Int), Constraint) -> Either SolverError ()
        verifyEdge ((x, y), c) = case (IntMap.lookup x types, IntMap.lookup y types) of
            (Just tx, Just ty) -> case c of
                Equal -> if tx == ty then Right () else Left $ InconsistentGraph x y Equal tx ty
                Plus  -> if updateType Plus tx == Just ty then Right () else Left $ InconsistentGraph x y Plus tx ty
                Minus -> if updateType Minus tx == Just ty then Right () else Left $ InconsistentGraph x y Minus tx ty
            _ -> error "Invalid nodes"


verifyAndSolve :: ConstraintGraph -> Either [SolverError] (IntMap.IntMap Type)
verifyAndSolve graph =
    case solveConstraints graph of
        Left err -> Left [err]
        Right t -> do
            verifyConstraints t graph
            return t

-- 
--
-- Recode a simple BFS algorithm
-- to propagate typing constraints.
--
-- This code is for debug purpose only.
--
bfsForest :: ConstraintGraph -> [(G.Vertex,Type)] -> IntMap.IntMap Type
bfsForest g roots = evalState (bfsForestM g roots >> get) IntMap.empty

bfsForestM :: ConstraintGraph -> [(G.Vertex,Type)] -> State (IntMap.IntMap Type) ()
bfsForestM g roots = bfsPrim $ map (\x -> [x]) roots
    where
        bfsTypeStep :: [(G.Vertex,Type)] -> State (IntMap.IntMap Type) [(G.Vertex,Type)]
        bfsTypeStep [] = return []
        bfsTypeStep ((x,tx):xs) = do
            visited <- get
            case IntMap.lookup x visited of
                Just _ -> return xs
                Nothing -> do
                    put $ IntMap.insert x tx visited
                    let neighbours = (graph g) A.! x
                    let newTypesM = map (\y -> (y, updateType ((elbl g) M.! (x,y)) tx)) neighbours
                    let newTypes = [(y, t) | (y, Just t) <- newTypesM]
                    bfsTypeStep (xs ++ newTypes)

        bfsSteps :: [[(G.Vertex,Type)]] -> State (IntMap.IntMap Type) [[(G.Vertex,Type)]]
        bfsSteps l = mapM bfsTypeStep l

        bfsPrim :: [[(G.Vertex,Type)]] -> State (IntMap.IntMap Type) ()
        bfsPrim l = do 
            newL <- bfsSteps l
            case any (not . null) newL of
                True -> bfsPrim newL
                False -> return ()

solveConstraintsBFS :: ConstraintGraph -> Either SolverError (IntMap.IntMap Type) 
solveConstraintsBFS g = do
                                let types        = bfsForest g $ IntMap.toList (csts g)
                                let allNodes     = IntSet.fromList $ G.vertices (graph g)
                                let touchedNodes = IntSet.fromList $ IntMap.keys types
                                let uncovered    = IntSet.difference allNodes touchedNodes
                                case IntSet.null uncovered of
                                    True  -> Right $ types
                                    False -> Left $ UncoveredNodes [uncovered]

verifyAndSolveBFS :: ConstraintGraph -> Either [SolverError] (IntMap.IntMap Type)
verifyAndSolveBFS graph =
    case solveConstraintsBFS graph of
        Left err -> Left [err]
        Right t -> do
            verifyConstraints t graph
            return t
