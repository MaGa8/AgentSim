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
  where floodBranch x lt rt = Branch x' (flood fb fl ol lt) (flood fb fl or rt)
          where (x', ol, or) = fb o x

type Range v = (v,v)        

data Pointer v = Pointer{ leftRange :: Range v, rightRange :: Range v, treeSize :: Int, treeHeight :: Int }

data Content d v = Content{ uids :: NonEmpty d, pos :: v }

type RangeTree d v = BinTree (Pointer v) (Content d v)

type RangeList d v = N.NonEmpty (d,v)

type Block d v = (Int,v,NonEmpty d)

-- | number of nodes in the range tree
rangeTreeSize :: RangeTree d v -> Int
rangeTreeSize = elimTree (\ptr _ _ -> treeSize ptr) (const 1)

makeRangeTree :: Either (Content d v) (RangeTree d v, RangeTree d v) -> RangeTree d v
makeRangeTree = either Leaf (\(lsub,rsub) -> Branch (makePointer lsub rsub) lsub rsub)

-- | sorts the sequence by the given predicate and builds the range tree
sortBuild :: (Eq v) => (v -> v -> Ordering) -> N.NonEmpty (d,v) -> RangeTree d v
sortBuild p = buildIfSorted . N.sortBy (\x1 x2 -> p (snd x1) (snd x2) )

-- | builds a range tree by recursively taking the median of a sorted sequence
buildIfSorted :: (Eq v) => RangeList d v -> RangeTree d v
buildIfSorted = splitTree2RangeTree . makeSplitTree . makeValueBlocks

makeSplitTree :: NonEmpty (Block d v) -> BinTree () (v, NonEmpty d)
makeSplitTree = unfoldTree (either arrangeSingle arrangeSplit .  splitByMedianValue)
  where arrangeSingle (xs,p) = Left (p,xs)
        arrangeSplit (lbs,_,rbs) = Right ((), lbs,rbs)

splitTree2RangeTree :: BinTree () (v, NonEmpty d) -> RangeTree d v
splitTree2RangeTree = drain deducePointer makeContent
  where deducePointer _ lsub rsub = makeRangeTree $ Right (lsub,rsub)
        makeContent (p,xs) = makeRangeTree $ Left Content{ uids = xs, pos = p }
                                           
splitByMedianValue :: NonEmpty (Block d v) -> Either (NonEmpty d,v) (NonEmpty (Block d v), v, NonEmpty (Block d v))
splitByMedianValue ((_,p,ids) :| []) = Left (ids,p)
splitByMedianValue blocks = Right (N.fromList leftBlocks,medianPos,N.fromList rightBlocks)
  where halfBlockSize = floor $ N.length blocks % 2
        (_,medianPos,_) = blocks N.!! halfBlockSize
        (leftBlocks,rightBlocks) = N.splitAt halfBlockSize blocks

-- | produces blocks of same value from a sorted list
makeValueBlocks :: (Eq v) => RangeList d v -> NonEmpty (Block d v)
makeValueBlocks ((n,p) :| tl) = N.fromList . reverse . execWriter . foldM collect iniv $ zip [1 ..] tl
  where iniv = (0,p, n :| [])
        collect (i,p',ids) (j,(n',p''))
          | p' == p'' = return (i,p',n' <| ids)
          | otherwise = tell [(i,p',ids)] >> return (j,p'', n' :| [])                          

-- question: would it be any use to build the tree lazily or does lazy evaluation already take care of this?
-- | insert a new id-position pair into the range tree
insert :: (v -> v -> Ordering) -> (d,v) -> RangeTree d v -> RangeTree d v
insert f pair@(x,p) = elimTree chooseSubtree integrateWithLeaf
  where chooseSubtree ptr lsub rsub
          | inRange f p (leftRange ptr) = reassemble (insert f pair lsub) rsub
          | inRange f p (rightRange ptr) = reassemble lsub (insert f pair rsub)
          | rangeTreeSize lsub <= rangeTreeSize rsub = reassemble (insert f pair lsub) rsub
          | otherwise = reassemble lsub (insert f pair rsub)
        reassemble lsub rsub = Branch (makePointer lsub rsub) lsub rsub
        integrateWithLeaf  con
          | f p (pos con) == EQ = Leaf con{ uids = x <| uids con }
          | f p (pos con) == LT = reassemble newLeaf oldLeaf
          | otherwise = reassemble oldLeaf newLeaf
          where newLeaf = Leaf Content{ uids = x :| [], pos = p }
                oldLeaf = Leaf con

-- | predicate if x is in the inclusive interval [l,r]
inRange :: (v -> v -> Ordering) -> v -> Range v -> Bool
inRange p x (l,r) = l `leq` x && x `leq` r
  where leq y z = let o = p y z in o == EQ || o == LT

makePointer :: RangeTree d v -> RangeTree d v -> Pointer v
makePointer lsub rsub = Pointer{ leftRange = lran, rightRange = rran, treeSize = lsiz + rsiz, treeHeight = max lhei rhei }
  where (lran, lsiz, lhei) = extractFromSub lsub
        (rran, rsiz, rhei) = extractFromSub rsub
        extractFromSub (Leaf con) = ((pos con, pos con),1,1)
        extractFromSub (Branch ptr _ _) = (uniteRange (leftRange ptr) (rightRange ptr), treeSize ptr, treeHeight ptr)

-- | merge two ranges into a new range assuming the first is left of the second
uniteRange :: Range v -> Range v -> Range v
uniteRange lran rran = (fst lran, snd rran)


delete :: (v -> v -> Ordering) -> (d,v) -> RangeTree d v -> Maybe (RangeTree d v)
delete f pair@(x,p) = elimTree chooseSubtree (const Nothing)
  where chooseSubtree ptr lsub rsub
          | inRange f p (leftRange ptr) = Just . makeRangeTree . maybe (fillIn rsub) (\lsub' -> Right (lsub',rsub)) $ delete f pair lsub
          | inRange f p (rightRange ptr) = Just . makeRangeTree . maybe (fillIn lsub) (\rsub' -> Right (lsub,rsub')) $ delete f pair rsub
          | otherwise = Just . makeRangeTree $ Right (lsub,rsub)
        fillIn = elimTree (\_ lsub rsub -> Right (lsub,rsub)) Left
        -- deleting a leaf is always nothing, because the parent's pointer range is tight

-- updates the position of a single element by UID
update :: (v -> v -> Ordering) -> d -> v -> v -> RangeTree d v -> RangeTree d v
update f x oldPos newPos = maybe singleton (insert f (x,newPos)) . delete f (x,oldPos)
  where singleton = makeRangeTree $ Left Content{ uids = x :| [], pos = newPos }
