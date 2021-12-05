

module MedianFind where

import Rank

import System.Random

import Control.Monad
import Control.Monad.State

size = 10^6
randomRange = (0, 10^9)
amount = 100

main :: IO ()
main = do
  gen <- getStdGen
  let randomLists = replicateM amount (getRandomList size) `evalState` randomRs randomRange gen
      exactMedians = map (pickMedian compare) randomLists
      approxMedians = map (sicilianMedian compare 5 size) randomLists
      ranges = map (\l -> (minimum l, maximum l)) randomLists
  mapM_ print $ zip3 exactMedians approxMedians ranges
  -- mapM_ (print . pickMedian compare) randomLists
  -- mapM_ (print . sicilianMedian compare 5 size) randomLists
  where
    medianDiff m1 m2 = maybe 0 abs $ (-) <$> m1 <*> m2

getRandomList :: Int -> State [Int] [Int]
getRandomList n = state (splitAt n)
-- getRandomList 0 = return []
-- getRandomList n = (:) <$> state (random g) <*> getRandomList (n-1)
