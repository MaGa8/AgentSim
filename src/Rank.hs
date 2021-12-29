{-# LANGUAGE TupleSections, ScopedTypeVariables #-}

module Rank
  (
    medianRank
  , pickMedian, pickAtRank, pickApproxMedian
  , partitionByMedian, approxPartitionByMedian
  , medianOfMedians, sicilianMedian
  ) where

import Data.List as L
import Data.Maybe
import Data.Ratio
import Data.Foldable as F
import qualified Data.Array.IArray as A

type Size = Int
type Rank = Int -- ^ rank is the number of elements smaller

-- | Choose median exactly.
pickMedian :: Foldable t => (a -> a -> Ordering) -> t a -> Maybe a
pickMedian fcmp xs = medianOfMedians fcmp (length xs) (medianRank $ length xs) 5 xs

-- | Chooses element whose rank is approximately the median.  No approximation guarantee.
pickApproxMedian :: forall t a. Foldable t =>
                    (a -> a -> Ordering) -- ^ comparator function computing Ordering of first w.r.t. latter
                 -> t a -> Maybe a
pickApproxMedian fcmp = uncurry (sicilianMedian fcmp 5) . boundsPair . fold2Array
  where
    boundsPair :: A.Array Int a -> (Int, A.Array Int a)
    boundsPair arr = (1 + uncurry subtract (A.bounds arr), arr)

pickAtRank :: (a -> a -> Ordering) -> Rank -> [a] -> Maybe a
pickAtRank fcmp rank xs = medianOfMedians fcmp (length xs) rank 5 xs

-- partitions list into values smaller or equal and values greater than the lower median 
partitionByMedian :: Foldable t => (a -> a -> Ordering) -> t a -> Maybe (a,[a],[a])
partitionByMedian fcmp xs = makePartition fcmp xs <$> pickMedian fcmp xs

approxPartitionByMedian :: Foldable t => (a -> a -> Ordering) -> t a -> Maybe (a, [a], [a])
approxPartitionByMedian fcmp xs = makePartition fcmp xs <$> pickApproxMedian fcmp xs

medianRank :: Int -> Int
medianRank = floor . (% 2) . subtract 1

partitionByPivot :: Foldable t => (a -> a -> Ordering) -> a -> t a -> (Compo a, Compo a, Compo a)
partitionByPivot fcmp piv = foldl' categorize (emptyCompo, emptyCompo, emptyCompo)
  where
    categorize (smaller, equal, greater) x = case fcmp piv x of
      GT -> (addToCompo smaller x, equal, greater)
      EQ -> (smaller, addToCompo equal x, greater)
      LT -> (smaller, equal, addToCompo greater x)

makePartition :: Foldable t => (a -> a -> Ordering) -> t a -> a -> (a, [a], [a])
makePartition fcmp xs med = let (smalls, equals, greats) = mkArrayPartition $ partitionByPivot fcmp med xs
                                (nsmalls, ngreats) = (arraySize smalls, arraySize greats)
                            in if nsmalls <= ngreats then (med, A.elems equals ++ A.elems smalls, A.elems greats) else (med, A.elems smalls, A.elems equals ++ A.elems greats)    

mkArrayPartition :: (Compo a, Compo a, Compo a) -> (A.Array Int a, A.Array Int a, A.Array Int a)
mkArrayPartition (c1, c2, c3) = (compo2Array c1, compo2Array c2, compo2Array c3)

-- | select element at index rank as in the median-of-medians algorithm
-- adapted to also work with duplicate elements
medianOfMedians :: Foldable t => (a -> a -> Ordering) -- ^ comparator: computes Ordering of the first with respect to the latter
                -> Int -- ^ number of elements in list
                -> Int -- ^ rank of the item to select
                -> Int -- ^ number of elements in a column
                -> t a -> Maybe a
medianOfMedians fcmp nelem rank chunkSize xs
  | null xs = Nothing
  | nelem <= chunkSize = Just . (!! rank) . L.sortBy fcmp $ F.toList xs            -- O(1)
  | pivotLowerRank <= rank && rank <= pivotUpperRank = Just pivot            -- O(1)
  | rank < pivotLowerRank = medianOfMedians fcmp nsmalls rank chunkSize smalls            -- O(smalls)
  | rank > pivotUpperRank = medianOfMedians fcmp ngreats (rank - nelem + ngreats) chunkSize greats            -- O(greats) where w.c. n = smalls+greats
  where
    -- require 3 passes over xs (last implicit over smalls, greats)
    pivot = fromJust $ findColMedianWorker fcmp nelem chunkSize xs -- O(?)
    (smalls, equals, greats) = mkArrayPartition $ partitionByPivot fcmp pivot xs -- O(n)
    (nsmalls, ngreats) = (arraySize smalls, arraySize greats)
    -- (nsmalls, ngreats) = (length smalls, length greats) -- O(n)
    (pivotLowerRank, pivotUpperRank) = (nsmalls, nelem - ngreats - 1) -- O(1)

-- | Choose approximate median by subsampling, no approximation guarantee exists.
sicilianMedian :: Foldable t =>
                  (a -> a -> Ordering) -- ^ compute Ordering of first w.r.t. latter
               -> Int -- ^ size of local neighborhood where median is chosen
               -> Int -- ^ number of elements in foldable
               -> t a -> Maybe a
sicilianMedian fcmp chunkSize nelem xs
  | nelem <= 10*chunkSize = pickMiddle . L.sortBy fcmp $ toList xs
  | otherwise = uncurry (flip (sicilianMedian fcmp chunkSize)) $ produceColMedians fcmp chunkSize xs

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

findColMedianWorker :: forall a t. (Foldable t) => (a -> a -> Ordering) -> Size -> Size -> t a -> Maybe a
findColMedianWorker fcmp nelem chunkSize = medianOfMedians fcmp nelem' (medianRank nelem') chunkSize . mkArray . produceColMedians fcmp chunkSize
  where
    nelem' = ceiling $ nelem % chunkSize
    mkArray :: ([a], Int) -> A.Array Int a
    mkArray (xs, size) = A.listArray (0, size - 1) xs

-- | Produces reversed list of local medians in nchunk-sized blocks.  Appends remainder.
produceColMedians :: Foldable t => (a -> a -> Ordering) -> Size -> t a -> Compo a
produceColMedians fcmp nchunk = finishup . foldl' (\tup x -> processGroup $ addToGroup x tup) ([], 0, [], 0)
  where
    processGroup (buffer, size, medians, nmeds)
      | size == nchunk = ([], 0, moveBufferMedian buffer medians, nmeds + 1)
      | otherwise = (buffer, size, medians, nmeds)
    moveBufferMedian buffer medians = maybe medians (`cons'` medians) . pickMiddle $ L.sortBy fcmp buffer
    addToGroup x (buffer, size, medians, nmeds) = (x : buffer, size + 1, medians, nmeds)
    finishup (buffer, size, medians, nmeds)
      | null buffer = (medians, nmeds)
      -- we append the whole remainder (its median is not the same as the others)
      | otherwise = (foldl' (flip cons') medians buffer, nmeds + 1)
    mkArray (_, _, meds, n) = A.listArray (0, n-1) meds

arraySize :: (Num i, A.IArray a e, A.Ix i) => a i e -> i
arraySize = (+ 1) . uncurry subtract . A.bounds

-- folds into reversed array indexed 0 to (n-1)
fold2Array :: (Foldable t, A.IArray a e, A.Ix i, Num i) => t e -> a i e
fold2Array = construct . foldl' countConcat (0, [])
  where
    countConcat (size, list) x = (size + 1, x : list)
    construct (size, list) = A.listArray (0, fromIntegral (size - 1)) list


cons' :: a -> [a] -> [a]
cons' x xs = x `seq` x : xs

type Compo a = ([a], Int)

emptyCompo :: Compo a
emptyCompo = ([], 0)

addToCompo :: Compo a -> a -> Compo a
addToCompo (xs, n) x = (cons' x xs, n+1)

compo2Array :: (Num i, A.Ix i, A.IArray a e) => Compo e -> a i e
compo2Array (xs, n) = A.listArray (0, fromIntegral $ n - 1) xs
