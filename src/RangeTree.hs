{-# LANGUAGE FlexibleContexts #-}

module RangeTree
  (
    -- RangeTree
    -- , sortBuild, buildIfSorted
  ) where

-- import Data.Tree
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty(NonEmpty(..), (<|))
import Data.Ratio
import Data.Maybe

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Writer

data BinTree a b = Branch a (BinTree a b) (BinTree a b) | Leaf b

-- | Yields the root of the tree wrapped in either Left (stop, reached the bottom) or Right (keep going)
root :: BinTree a b -> Either b a
root (Branch x _ _) = Right x
root (Leaf y) = Left y 

children :: BinTree a b -> Maybe (BinTree a b, BinTree a b)
children (Branch _ lt rt) = Just (lt, rt)
children (Leaf _) = Nothing

unfoldTree :: (a -> Either c (b, a, a)) -> a -> BinTree b c
unfoldTree f = either Leaf (\(x, ol, or) -> Branch x (unfoldTree f ol) (unfoldTree f or)) . f

elimTree :: (a -> BinTree a b -> BinTree a b -> c) -> (b -> c) -> BinTree a b -> c
elimTree fb _ (Branch x lt rt) = fb x lt rt
elimTree _ fl (Leaf y) = fl y

mapTree :: (a -> c) -> (b -> d) -> BinTree a b -> BinTree c d
mapTree fb fl = elimTree (\x lt rt -> Branch (fb x) (mapTree fb fl lt) (mapTree fb fl rt)) (Leaf . fl)

drain :: (a -> c -> c -> c) -> (b -> c) -> BinTree a b -> c
drain fb fl = elimTree (\x lt rt -> fb x (drain fb fl lt) (drain fb fl rt)) fl

flood :: (a -> b -> (d, a, a)) -> (a -> c -> e) -> a -> BinTree b c -> BinTree d e
flood fb fl o = elimTree floodBranch (Leaf . fl o)
  where
    floodBranch x lt rt = Branch x' (flood fb fl ol lt) (flood fb fl or rt)
      where
        (x', ol, or) = fb o x

data Pointer v = Pointer{ leftRange :: (v,v), rightRange :: (v,v), size :: Int, height :: Int }

data Content d v = Content{ uids :: NonEmpty d, pos :: v }

type RangeTree d v = BinTree (Pointer v) (Content d v)

type Range d v = N.NonEmpty (d,v)

-- | sorts the sequence by the given predicate and builds the range tree
sortBuild :: (Eq v) => (v -> v -> Ordering) -> N.NonEmpty (d,v) -> RangeTree d v
sortBuild p = buildIfSorted . N.sortBy (\x1 x2 -> p (snd x1) (snd x2) )

-- | builds a range tree by recursively taking the median of a sorted sequence
buildIfSorted :: (Eq v) => Range d v -> RangeTree d v
buildIfSorted = unfoldTree makeRangeIfSorted . makeValueBlocks
  where makeRangeIfSorted = blocks2Node

type Block d v = (Int,v,NonEmpty d)

blocks2Node :: NonEmpty (Block d v) -> Either (Content d v) (Pointer v, NonEmpty (Block d v), NonEmpty (Block d v))
-- range2Node ((n,p) :| []) = Left Content{ uid=n, pos=p }
blocks2Node bs = either makeLeaf makeInner . splitByMedianValue $ bs
  where makeLeaf (ids,p) = Left $ Content{ uids = ids, pos = p }
        makeInner (lbs,_,rbs) = Right (Pointer{ leftRange = blockBounds lbs
                                                      , rightRange = blockBounds rbs
                                                      , size = blockCumSize bs
                                                      , height = -1 }
                                    , lbs, rbs)
        blockBounds = (snd3 *** snd3) . (N.head &&& N.last)
        snd3 (_,x,_) = x
        blockCumSize = sum . fmap (\(_,_,ids) -> length ids)

                                             

splitByMedianValue :: NonEmpty (Block d v) -> Either (NonEmpty d,v) (NonEmpty (Block d v), v, NonEmpty (Block d v))
splitByMedianValue ((_,p,ids) :| []) = Left (ids,p)
splitByMedianValue blocks = Right (N.fromList leftBlocks,medianPos,N.fromList rightBlocks)
  where halfBlockSize = floor $ N.length blocks % 2
        (_,medianPos,_) = blocks N.!! halfBlockSize
        (leftBlocks,rightBlocks) = N.splitAt halfBlockSize blocks

-- | produces blocks of same value from a sorted list
makeValueBlocks :: (Eq v) => Range d v -> NonEmpty (Block d v)
makeValueBlocks ((n,p) :| tl) = N.fromList . reverse . execWriter . foldM collect iniv $ zip [1 ..] tl
  where iniv = (0,p, n :| [])
        collect (i,p',ids) (j,(n',p''))
          | p' == p'' = return (i,p',n' <| ids)
          | otherwise = tell [(i,p',ids)] >> return (j,p'', n' :| [])                          


splitByMedian :: N.NonEmpty a -> ([a], a, [a])
splitByMedian ps = (\(loMid, hi) -> (init loMid, last loMid, hi)) $ N.splitAt medpos ps
  where medpos = floor $ N.length ps % 2

{- 
insert :: Ord v => v -> RangeTree v -> RangeTree v -- is it better to assume v is not in Ord at the cost of more parameters?
insert x t = foldTree chooseSub t
  where chooseSub (Point x') = if x < x'
                               then Tree{rootLabel=Stretch x (x, x'), subForest=[Point x']}
                               else Tree{rootLabel=Stretch x' (x', x), subForest=

-- delete :: v -> RangeTree v -> RangeTree v


-- update :: (v -> v) -> RangeTree v -> RangeTree v
-}
