module Sim
  (
    Pop, Book, Place, Arena
  , step
  ) where

-- imports
-- data
import Data.Map

-- control
import Control.Monad.State

-- custom
import Agent

-- definitions
-- data
-- for later: want to update tree using new positions; forget about that for now
data Loc i v = Loc{locmap :: Book i v, loctree :: Place i v} 

-- aliases
type Pop i a = Map i a
type Book i v = Map i v
type Place i v = Tree2d v i
type Arena i v a = State (Place i v) (Pop i a)
type Repo i m = Map i [m]

-- |perform one step of the simulation
step :: (Agent a i v m) => Arena i v (a i v m) -> Arena i v (a i v m)
step arena = do
  pop <- arena
  -- plc <- get    for now: rebuild from scratch
  let plc = buildRange pop
  let popTalked = converse plc pop
  let popComputed = locCompute popTalked
  -- put $ localize plc popComputed
  return popComputed

-- |build the 2d tree containing the population
buildRange :: (Agent a i v m) => Pop i (a i v m) -> Place i v


-- |build temporary communication graph
-- this is already implicit through range tree, too expensive to materialize?
-- buildAdjacency :: Place i v -> [(i, [i])]

-- |generate all messages, distribute them among the neighborhood and perform all listens
converse :: (Agent a i v m) => Place i v -> Pop i (a i v m) -> Pop i (a i v m)


-- |execute the local computation
locCompute :: (Agent a i v m) => Pop i (a i v m) -> Pop i (a i v m)



