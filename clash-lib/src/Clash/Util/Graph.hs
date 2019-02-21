{-|
  Copyright   :  (C) 2018, QBayLogic
  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  Christiaan Baaij <christiaan.baaij@gmail.com>

  Collection of utilities
-}
module Clash.Util.Graph (topSort, reverseTopSort, TopSortError(..)) where

import           Data.Tuple            (swap)
import           Data.Foldable         (foldlM)
import qualified Data.IntMap.Strict    as IntMap
import qualified Data.IntSet           as IntSet

data Marker
  = Temporary
  | Permanent

data TopSortError
  = CycleDetected Int
  -- ^ Cycle detected. Node @a@ was part of the cycle.
  | EdgesNoNodes
  -- ^ Edges specified, but no nodes
  | MissingNode Int
  -- ^ Node @a@ mentioned in edge list, but not present in node list

instance Show TopSortError where
  show (CycleDetected n) =
    "CycleDetected: Can't sort non-DAG. Node with id " ++ show n ++ " was part of cycle."
  show EdgesNoNodes =
    "EdgesNoNodes: Node list was empty, but edges non-empty"
  show (MissingNode n) =
    "MissingNode: node with id " ++ show n ++ " part of an edge, but not in node list"

headSafe :: [a] -> Maybe a
headSafe [] = Nothing
headSafe (a:_) = Just a

topSortVisit'
  :: IntMap.IntMap [Int]
  -- ^ Edges
  -> IntSet.IntSet
  -- ^ Unmarked nodes
  -> IntMap.IntMap Marker
  -- ^ Marked nodes
  -> [Int]
  -- ^ Sorted so far
  -> Int
  -- ^ Node to visit
  -> Either TopSortError (IntSet.IntSet, IntMap.IntMap Marker, [Int])
topSortVisit' edges unmarked marked sorted node =
  case IntMap.lookup node marked of
    Just Permanent -> Right (unmarked, marked, sorted)
    Just Temporary -> Left (CycleDetected node)
    Nothing -> do
      let marked'   = IntMap.insert node Temporary marked
      let unmarked' = IntSet.delete node unmarked
      let nodeToM   = IntMap.findWithDefault [] node edges
      (unmarked'', marked'', sorted'') <-
        foldlM visit (unmarked', marked', sorted) nodeToM
      let marked''' = IntMap.insert node Permanent marked''
      return (unmarked'', marked''', node : sorted'')
  where
    visit (unmarked', marked', sorted') node' =
      topSortVisit' edges unmarked' marked' sorted' node'

topSortVisit
  :: IntMap.IntMap [Int]
  -- ^ Edges
  -> IntSet.IntSet
  -- ^ Unmarked nodes
  -> IntMap.IntMap Marker
  -- ^ Marked nodes
  -> [Int]
  -- ^ Sorted so far
  -> Int
  -- ^ Node to visit
  -> Either TopSortError (IntSet.IntSet, IntMap.IntMap Marker, [Int])
topSortVisit edges unmarked marked sorted node = do
  (unmarked', marked', sorted') <-
    topSortVisit' edges unmarked marked sorted node

  case headSafe (IntSet.toList unmarked') of
    Nothing    -> return (unmarked', marked', sorted')
    Just node' -> topSortVisit edges unmarked' marked' sorted' node'

-- | See: https://en.wikipedia.org/wiki/Topological_sorting. This function
-- errors if edges mention nodes not mentioned in the node list or if the
-- given graph contains cycles.
topSort
  :: [(Int, a)]
  -- ^ Nodes
  -> [(Int, Int)]
  -- ^ Edges
  -> Either TopSortError [a]
  -- ^ Error message or topologically sorted nodes
topSort []             []     = Right []
topSort []             _edges = Left EdgesNoNodes
topSort nodes@(node:_)  edges = do
  _ <- mapM (\(n, m) -> checkNode n >> checkNode m) edges

  (_, _, sorted) <-
    topSortVisit edges' (IntMap.keysSet nodes') IntMap.empty [] (fst node)

  mapM lookup' sorted
    where
      nodes' = IntMap.fromList nodes
      edges' = foldl insert IntMap.empty edges

      -- Construction functions for quick lookup of edges from n to m, given n
      insert im (n, m)    = IntMap.alter (insert' m) n im
      insert' m Nothing   = Just [m]
      insert' m (Just ms) = Just (m:ms)

      -- Lookup node in nodes map. If not present, yield error
      lookup' n =
        case IntMap.lookup n nodes' of
          Nothing -> Left (MissingNode n)
          Just n' -> Right n'

      -- Check if edge is valid (i.e., mentioned nodes are in node list)
      checkNode n
        | IntMap.notMember n nodes' = Left (MissingNode n)
        | otherwise                 = Right n

-- | Same as `reverse (topSort nodes edges)` if alternative representations are
-- considered the same. That is, topSort might produce multiple answers and
-- still deliver on its promise of yielding a topologically sorted node list.
-- Likewise, this function promises __one__ of those lists in reverse, but not
-- necessarily the reverse of topSort itself.
reverseTopSort
  :: [(Int, a)]
  -- ^ Nodes
  -> [(Int, Int)]
  -- ^ Edges
  -> Either TopSortError [a]
  -- ^ Reversely, topologically sorted nodes
reverseTopSort nodes edges =
  topSort nodes (map swap edges)
