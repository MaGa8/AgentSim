

module MedianFind where

import Rank
import System.Random

import Control.Monad
import Control.Monad.State

size = 10^6
amount = 100

main :: IO ()
main = do
  gen <- getStdGen
  let randomLists = replicateM amount (getRandomList size) `evalState` randoms gen
  mapM_ print $ map (pickMedian compare) randomLists

getRandomList :: Int -> State [Int] [Int]
getRandomList n = state (splitAt n)
-- getRandomList 0 = return []
-- getRandomList n = (:) <$> state (random g) <*> getRandomList (n-1)
