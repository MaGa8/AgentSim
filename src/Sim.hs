{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
module Sim
  (
    module Agent
  , Map, M.keys, M.lookup
  , initPositions, sim
  ) where

-- imports
-- data
import Data.Map(Map)
import qualified Data.Map as M
import MultiRangeTree(Comparator, ComparatorSeq)
import qualified MultiRangeTree as MRT
import qualified Data.List.NonEmpty as N
import Data.Maybe
import Data.Bifunctor


-- control
import Control.Monad.State

-- custom
import Agent

initPositions :: (Ord a) => [Agent p m a] -> [p] -> Map (Agent p m a) p
initPositions agents positions = M.fromList $ zip agents positions

sim :: (Ord a) => ComparatorSeq p -> Map (Agent p m a) p -> Map (Agent p m a) p
sim comps positions = react positions . produceMessages positions $ determineNeighbors comps positions

determineNeighbors :: (Ord a) => MRT.ComparatorSeq p -> Map (Agent p m a) p -> Map (Agent p m a) [Agent p m a]
determineNeighbors comps agents
  | null agents = mempty
  | otherwise = M.mapWithKey queryFun agents
  where
    index = MRT.buildMultiRangeTree comps (N.fromList  $ M.assocs agents)
    queryFun agent pos = map fst $ MRT.query (N.toList comps) (agentSee agent pos) index

produceMessages :: (Ord a) => Map (Agent p m a) p -> Map (Agent p m a) [Agent p m a] -> Map (Agent p m a) [m]
produceMessages positions neighbors = M.foldlWithKey (\messages ag pos -> mergeMaps (`M.lookup` agents) messages $ makeTalk ag pos) mempty positions
  where
    -- use to lookup complete agents given core
    agents = M.fromList . map ((\ag -> (core ag, ag)) . fst) $ M.toList positions
    makeTalk ag pos = maybe mempty (agentTalk ag pos . associateJoin core positions) $ M.lookup ag neighbors

mergeMaps :: (Ord b) => (a -> Maybe b) -> Map b [c] -> Map a c -> Map b [c]
mergeMaps f = M.foldlWithKey (\mmap k v -> maybe mmap (\k' -> M.insertWith (++) k' [v] mmap) $ f k)

associateJoin :: (Ord a, Ord b) => (a -> b) -> Map a c -> [a] -> Map b c
associateJoin f full = M.fromList . mapMaybe (\x -> (f x,) <$> M.lookup x full)

react :: (Ord a) => Map (Agent p m a) p -> Map (Agent p m a) [m] -> Map (Agent p m a) p
react = combineMaps (\ag pos messIns -> first (updateCore ag) $ agentAct ag pos messIns)

combineMaps :: (Ord a, Ord d) => (a -> b -> c -> (d,e)) -> Map a b -> Map a c -> Map d e
combineMaps f m1 m2 = M.foldlWithKey (\merger k1 v1 -> maybe merger (\v2 -> insertByPair (f k1 v1 v2) merger) $ M.lookup k1 m2) mempty m1
  where
    insertByPair (k,v) m = M.insert k v m
