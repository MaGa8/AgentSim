{-# LANGUAGE BangPatterns #-}

module MrtConstruction where

import MultiRangeTree

import Data.Foldable
import qualified Data.List.NonEmpty as E

import Control.Monad
import Control.Monad.State

import System.Random

main :: IO ()
main = do
  gen <- getStdGen
  runMockup gen >> return ()

numCases, numPositions :: Int
numCases = 100
numPositions = 10^4
minpos, maxpos, radius :: Int
minpos = 0
maxpos = 10^7
radius = 25

runMockup :: (RandomGen g) => g -> IO Int
runMockup gen = foldlM mkOutput 0 . map forceAllQueries $ generateRandomPositions gen numCases numPositions

type Pos = (Int, Int)

pos2Query :: Pos -> Query Pos
pos2Query (x,y) = ((x - radius, y - radius), (x + radius, y + radius))

comparators :: [Pos -> Pos -> Ordering]
comparators = [ \(x,_) (y,_) -> compare x y, \(_,x) (_,y) -> compare x y]

generateRandomPositions :: (RandomGen g) => g -> Int -> Int -> [[Pos]]
generateRandomPositions gen ncases npos = flip evalState gen . replicateM ncases $ replicateM npos generatePosition
  where
    generatePosition = (,) <$> state (randomR (minpos, maxpos)) <*> state (randomR (minpos, maxpos))

forceAllQueries :: [Pos] -> ()
forceAllQueries poss = forceAll . queryAll $ build
  where
    insts = zip [1 ..] poss
    build = buildMultiRangeTree (E.fromList MrtConstruction.comparators) $ E.fromList insts
    queryAll mrt = concatMap (\(i,pos) -> query (pos2Query pos) mrt) insts
    forceAll = foldl' (\none (i, _) -> seq i none) ()

mkOutput :: Int -> () -> IO Int
mkOutput n x = let n' = seq x (n+1)
               in print n >> return n'
