{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
module Sim
  (
    module Agent
  , Map, M.keys, M.lookup
  , initPositions, sim, simDebug
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
import Debug.Trace

initPositions :: (Ord a) => [Agent d p m a] -> [p] -> Map (Agent d p m a) p
initPositions agents positions = M.fromList $ zip agents positions

sim :: (Ord d) => ComparatorSeq p -> [Agent d p m a] -> [Agent d p m a]
sim comps positions = (`react` positions) . produceMessages $ determineNeighbors comps positions

pipeTrace :: (a -> String) -> a -> a
pipeTrace f x = trace (f x) x

simDebug :: (Ord d) => (Map d [m] -> String) -> ([Agent d p m a] -> String) -> ComparatorSeq p -> [Agent d p m a] -> [Agent d p m a]
simDebug fOutMessage fOutAgent comps positions = pipeTrace fOutAgent . (`react` positions) . pipeTrace fOutMessage . produceMessages $ determineNeighbors comps positions

determineNeighbors :: MRT.ComparatorSeq p -> [Agent d p m a] -> [(Agent d p m a, [Agent d p m a])]
determineNeighbors comps agents = map (\ag -> (ag, map fst $ MRT.query (N.toList comps) (agentSee ag) index)) agents
  where 
    index = MRT.buildMultiRangeTree comps . N.fromList $ map (\ag -> (ag, getPos ag)) agents
{-
  | null agents = mempty
  | otherwise = M.mapWithKey queryFun agents
  where
    index = MRT.buildMultiRangeTree comps (N.fromList  $ M.assocs agents)
    queryFun agent pos = map fst $ MRT.query (N.toList comps) (agentSee agent pos) index
-}

-- responsible for 62% of running time! A lot of it comes down to mergeMaps and associateJoin
-- produceMessages :: (Ord a) => Map (Agent d p m a) p -> Map (Agent d p m a) [Agent d p m a] -> Map (Agent d p m a) [m]
-- produceMessages positions neighbors = M.foldlWithKey' (\messages ag pos -> mergeMaps (`M.lookup` agents) messages $ makeTalk ag pos) mempty positions
  -- where
    -- use to lookup complete agents given core
    -- agents = M.fromList . map ((\ag -> (core ag, ag)) . fst) $ M.toList positions
    -- can we get around building these intermediate maps?
    -- makeTalk ag pos = maybe mempty (agentTalk ag pos . associateJoin core positions) $ M.lookup ag neighbors

strictCons :: a -> [a] -> [a]
strictCons x xs = x `seq` x : xs

produceMessages :: (Ord d) => [(Agent d p m a, [Agent d p m a])] -> Map d [m]
produceMessages = collect . map makeTalk
  where
    makeTalk (ag,neighbors) = agentTalk ag (map (\nag -> (getIdent nag, core nag, getPos nag)) neighbors)
    collect = M.fromListWith (\[m] -> (m : )) . map (second return) . concat

mergeMaps :: (Ord b) => (a -> Maybe b) -> Map b [c] -> Map a c -> Map b [c]
mergeMaps f = M.foldlWithKey' (\mmap k v -> maybe mmap (\k' -> M.insertWith (++) k' [v] mmap) $ f k)

associateJoin :: (Ord a, Ord b) => (a -> b) -> Map a c -> [a] -> Map b c
associateJoin f full = M.fromList . mapMaybe (\x -> (f x,) <$> M.lookup x full)

react :: (Ord d) => Map d [m] -> [Agent d p m a] -> [Agent d p m a]
react postbox = map (\ag -> updateAgent ag . maybe (agentAct ag []) (agentAct ag) $ M.lookup (getIdent ag) postbox)
  where
    updateAgent ag (newcore, newpos) = newcore `seq` newpos `seq` (`updatePos` newpos) $ updateCore ag newcore

{-
  combineMaps (\ag maybePos maybeMessIns -> handleMessages (updateAgent ag) (updateAgent ag) maybeMessIns <$> maybePos)
  where
    handleMessages none_fun some_fun maybeMsgs pos = maybe (none_fun pos []) (some_fun pos) maybeMsgs
    updateAgent ag pos = first (\core -> ag{core = core}) . agentAct ag pos
-}

-- performance ok
combineMaps :: (Ord a, Ord d) => (a -> Maybe b -> Maybe c -> Maybe (d,e)) -> Map a b -> Map a c -> Map d e
combineMaps f m1 m2 = M.union (combineMapsHalf leftCombiner part1 m2) (combineMapsHalf rightCombiner part2 m1)
  where
    part1 = M.mapWithKey (\k v1 -> f k (Just v1)) m1
    part2 = M.mapWithKey (\k v2 mv1 -> f k mv1 (Just v2)) m2
    leftCombiner _ fapp mk2 = fapp mk2
    rightCombiner _ fapp mk1 = fapp mk1

-- | inserts result of combination for all keys of m1
combineMapsHalf :: (Ord a, Ord d) => (a -> b -> Maybe c -> Maybe (d,e)) -> Map a b -> Map a c -> Map d e
combineMapsHalf f m1 m2 = M.foldlWithKey' (\merger k1 v1 -> maybe merger (insertPair merger) . f k1 v1 $ M.lookup k1 m2) mempty m1
  where
    insertPair m (k,v) = M.insert k v m
    
