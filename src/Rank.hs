
module Rank
  (
    medianRank
  , pickMedian, pickAtRank
  , partitionByPivot, partitionByMedian
  ) where

import Data.List as L
import Data.Maybe
import Data.Ratio

type Size = Int
type Rank = Int -- ^ rank is the number of elements smaller

partitionByPivot :: (a -> a -> Ordering) -> a -> [a] -> ([a],[a],[a])
partitionByPivot fcmp piv = foldl categorize ([],[],[])
  where
    categorize (smaller, equal, greater) x = case fcmp piv x of
      GT -> (x : smaller, equal, greater)
      EQ -> (smaller, x : equal, greater)
      LT -> (smaller, equal, x : greater)

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
    pickColMid = fromJust . pickMiddle . L.sortBy fcmp
    nelem' = ceiling $ nelem % chunkSize
    -- subtract one because it's #elements smaller, pick lower median
    medRank = floor . (% 2) $ nelem' - 1

-- | select element at index rank as in the median-of-medians algorithm
-- adapted to also work with duplicate elements
medianOfMediansWorker :: (a -> a -> Ordering) -- ^ comparator: computes Ordering of the first with respect to the latter
                -> Int -- ^ number of elements in list
                -> Int -- ^ rank of the item to select
                -> Int -- ^ number of elements in a column
                -> [a] -> Maybe a
medianOfMediansWorker _ _ _ _ [] = Nothing
medianOfMediansWorker fcmp nelem rank chunkSize xs
  | nelem <= chunkSize = Just $ L.sortBy fcmp xs !! rank
  | pivotLowerRank <= rank && rank <= pivotUpperRank = Just pivot
  | rank < pivotLowerRank = medianOfMediansWorker fcmp nsmalls rank chunkSize smalls
  | rank > pivotUpperRank = medianOfMediansWorker fcmp ngreats (rank - nelem + ngreats) chunkSize greats
  where 
    pivot = fromJust $ findColMedianWorker fcmp nelem chunkSize xs
    (smalls, equals, greats) = partitionByPivot fcmp pivot xs 
    (nsmalls, ngreats) = (length smalls, length greats)
    (pivotLowerRank, pivotUpperRank) = (nsmalls, nelem - ngreats - 1)

pickMedian :: (a -> a -> Ordering) -> [a] -> Maybe a
pickMedian fcmp xs = medianOfMediansWorker fcmp (length xs) (medianRank $ length xs) 5 xs

pickAtRank :: (a -> a -> Ordering) -> Rank -> [a] -> Maybe a
pickAtRank fcmp rank xs = medianOfMediansWorker fcmp (length xs) rank 5 xs

-- partitions list into values smaller or equal and values greater than the lower median 
partitionByMedian :: (a -> a -> Ordering) -> [a] -> Maybe (a,[a],[a])
partitionByMedian fcmp xs = makePartition <$> pickMedian fcmp xs
  where
    makePartition med = let (smalls, equals, greats) = partitionByPivot fcmp med xs
                        in (med, smalls ++ equals, greats)
