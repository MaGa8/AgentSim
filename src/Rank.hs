{-# LANGUAGE TupleSections #-}

module Rank
  (
    medianRank
  , pickMedian, pickAtRank
  , partitionByPivot, partitionByMedian
  ) where

import Data.List as L
import Data.Maybe
import Data.Ratio
import Data.Foldable as F
import qualified Data.Array.IArray as A

type Size = Int
type Rank = Int -- ^ rank is the number of elements smaller

cons' :: a -> [a] -> [a]
cons' x xs = x `seq` x : xs

-- lazyness only pays off if we're not scanning over the two biggest lists afterwards!
partitionByPivot :: (a -> a -> Ordering) -> a -> [a] -> ([a],[a],[a])
partitionByPivot fcmp piv = foldl categorize ([],[],[])
  where
    categorize (smaller, equal, greater) x = case fcmp piv x of
      GT -> (x : smaller, equal, greater)
      EQ -> (smaller, x : equal, greater)
      LT -> (smaller, equal, x : greater)

type Compo a = ([a], Int)

emptyCompo :: Compo a
emptyCompo = ([], 0)

addToCompo :: Compo a -> a -> Compo a
addToCompo (xs, n) x = (cons' x xs, n+1)

partitionByPivot' :: Foldable t => (a -> a -> Ordering) -> a -> t a -> (A.Array Int a, A.Array Int a, A.Array Int a)
partitionByPivot' fcmp piv = mkArrays . foldl' categorize (emptyCompo, emptyCompo, emptyCompo)
  where
    categorize (smaller, equal, greater) x = case fcmp piv x of
      GT -> (addToCompo smaller x, equal, greater)
      EQ -> (smaller, addToCompo equal x, greater)
      LT -> (smaller, equal, addToCompo greater x)
    mkArrays (smalls, equals, greats) = let constr (xs, size) = A.listArray (0, size - 1) xs
                                        in (constr smalls, constr equals, constr greats)

groupsOfN :: Int -> [a] -> [[a]]
groupsOfN n xs = g : if null xs' then [] else groupsOfN n xs'
  where (g,xs') = splitAt n xs

-- | chooses the lower middle of the list
pickMiddle :: [a] -> Maybe a
pickMiddle [] = Nothing
pickMiddle xs = helper xs xs
  where
    helper (y : _) [_] = Just y
    helper (y : _) [_,_] = Just y
    helper (_ : ys) (_ : _ : zs) = helper ys zs

medianRank :: Int -> Int
medianRank = floor . (% 2) . subtract 1

-- | selects the lower median from the list
findColMedianWorker :: (a -> a -> Ordering) -> Size -> Size -> [a] -> Maybe a
findColMedianWorker fcmp nelem chunkSize = medianOfMediansWorker fcmp nelem' (medianRank nelem') chunkSize . map pickColMid . groupsOfN chunkSize
  where
    -- Really slow for what it does.  Ensure groups themselves are evaluated strictly
    pickColMid = fromJust . pickMiddle . L.sortBy fcmp
    nelem' = ceiling $ nelem % chunkSize
    -- subtract one because it's #elements smaller, pick lower median
    medRank = floor . (% 2) $ nelem' - 1

findColMedianWorker' :: Foldable t => (a -> a -> Ordering) -> Size -> Size -> t a -> Maybe a
findColMedianWorker' fcmp nelem chunkSize = medianOfMediansWorker fcmp nelem' (medianRank nelem') chunkSize . produceColMedians fcmp chunkSize
  where
    nelem' = ceiling $ nelem % chunkSize

produceColMedians :: Foldable t => (a -> a -> Ordering) -> Size -> t a -> A.Array Int a
produceColMedians fcmp nchunk = mkArray . finishup . foldl' (\tup x -> processGroup $ addToGroup x tup) ([], 0, [], 0)
  where
    processGroup (buffer, size, medians, nmeds)
      | size == nchunk = ([], 0, moveBufferMedian buffer medians, nmeds + 1)
      | otherwise = (buffer, size, medians, nmeds)
    moveBufferMedian buffer medians = maybe medians (`cons'` medians) . pickMiddle $ L.sortBy fcmp buffer
    addToGroup x (buffer, size, medians, nmeds) = (x : buffer, size + 1, medians, nmeds)
    finishup a@(buffer, size, medians, nmeds)
      | null buffer = a
      | otherwise = ([], 0, moveBufferMedian buffer medians, nmeds + 1)
    mkArray (_, _, meds, n) = A.listArray (0, n-1) meds

arraySize :: (Num i, A.IArray a e, A.Ix i) => a i e -> i
arraySize = (+ 1) . uncurry subtract . A.bounds

-- | select element at index rank as in the median-of-medians algorithm
-- adapted to also work with duplicate elements
medianOfMediansWorker :: Foldable t => (a -> a -> Ordering) -- ^ comparator: computes Ordering of the first with respect to the latter
                -> Int -- ^ number of elements in list
                -> Int -- ^ rank of the item to select
                -> Int -- ^ number of elements in a column
                -> t a -> Maybe a
medianOfMediansWorker fcmp nelem rank chunkSize xs
  | null xs = Nothing
  | nelem <= chunkSize = Just . (!! rank) . L.sortBy fcmp $ F.toList xs            -- O(1)
  | pivotLowerRank <= rank && rank <= pivotUpperRank = Just pivot            -- O(1)
  | rank < pivotLowerRank = medianOfMediansWorker fcmp nsmalls rank chunkSize smalls            -- O(smalls)
  | rank > pivotUpperRank = medianOfMediansWorker fcmp ngreats (rank - nelem + ngreats) chunkSize greats            -- O(greats) where w.c. n = smalls+greats
  where
    -- require 3 passes over xs (last implicit over smalls, greats)
    pivot = fromJust $ findColMedianWorker' fcmp nelem chunkSize xs -- O(?)
    (smalls, equals, greats) = partitionByPivot' fcmp pivot xs -- O(n)
    (nsmalls, ngreats) = (arraySize smalls, arraySize greats)
    -- (nsmalls, ngreats) = (length smalls, length greats) -- O(n)
    (pivotLowerRank, pivotUpperRank) = (nsmalls, nelem - ngreats - 1) -- O(1)


pickMedian :: (a -> a -> Ordering) -> [a] -> Maybe a
pickMedian fcmp xs = medianOfMediansWorker fcmp (length xs) (medianRank $ length xs) 5 xs

pickAtRank :: (a -> a -> Ordering) -> Rank -> [a] -> Maybe a
pickAtRank fcmp rank xs = medianOfMediansWorker fcmp (length xs) rank 5 xs

-- partitions list into values smaller or equal and values greater than the lower median 
partitionByMedian :: (a -> a -> Ordering) -> [a] -> Maybe (a,[a],[a])
partitionByMedian fcmp xs = makePartition <$> pickMedian fcmp xs
  where
    makePartition med = let (smalls, equals, greats) = partitionByPivot' fcmp med xs
                            (nsmalls, ngreats) = (arraySize smalls, arraySize greats)
                        in if nsmalls <= ngreats then (med, A.elems equals ++ A.elems smalls, A.elems greats) else (med, A.elems smalls, A.elems equals ++ A.elems greats)
