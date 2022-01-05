{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module MultiRangeTree
  (
  MultiRangeTree(..), Range, Query, Pointer(..), Content(..)
  , contentValues, contentKeys
  , Answer(..), elimAnswer
  , contains, disjoint, checkQuery
  , Comparator, ComparatorSeq
  , buildMultiRangeTree, query
  -- re-export selected Nest functions
  , module BinTree, Nest, NestNode
  , isFlat, isLeaf
  , root, roots, children, nest
  , mapNest, flood, floodFull, drain, echo, zipNest
  , prettyPrintNest
  ) where

import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty(NonEmpty(..), (<|))
import qualified Data.List as L
import Data.Bifunctor
import Data.Maybe
import Data.Ratio
import Data.Foldable as F

import qualified BinTree as B
import BinTree(BinTree(..))

import Control.Applicative
import Control.Arrow((&&&))
import Control.Exception

import Debug.Trace as Dbg

import Rank
import Nest

type Size = Int
type Range v = (v,v)

data Pointer a = Pointer{ pointerSize :: Size -- ^ number of points assigned to subtree
                        , pointerPivot :: a -- ^ greatest value in the left subtree
                        } deriving Show

newtype Content k v = Content{ contents :: NonEmpty (k,v) } deriving Show

contentValues :: Content k v -> NonEmpty v
contentValues = N.map snd . contents

contentKeys :: Content k v -> NonEmpty k
contentKeys = N.map fst . contents

type Comparator a = a -> a -> Ordering
type ComparatorSeq a = NonEmpty (Comparator a)

data MultiRangeTree k v = MultiRangeTree{ comparators :: ComparatorSeq v, getMultiRangeTree :: Nest (Pointer v) (Content k v) } 

type Inst k v = (k,v)

cmpBySnd f (_,x) (_,y) = f x y

buildMultiRangeTree :: ComparatorSeq v -> NonEmpty (Inst k v) -> MultiRangeTree k v
buildMultiRangeTree (f :| fs) points = MultiRangeTree{ comparators = f :| fs, getMultiRangeTree = buildMultiRangeTreeWorker (f : fs) top bottoms }
  where
    top = L.sortBy (cmpBySnd f) $ N.toList points
    bottoms = map (\f' -> L.sortBy (cmpBySnd f') $ N.toList points) fs

buildMultiRangeTreeWorker :: [Comparator v] -> [Inst k v] -> [[Inst k v]] -> Nest (Pointer v) (Content k v)
buildMultiRangeTreeWorker [f] top [] = Flat . B.mapTree mkPointer mkContent $ subdivide f top []
buildMultiRangeTreeWorker _ _ [] = error "Bottoms can't be empty while there's > 1 comparator."
buildMultiRangeTreeWorker (f : fs) top bottoms = Nest . nestTree (expandBottom fs) $ subdivide f top bottoms

type BinTreeU a = BinTree a a

type Component k v = (v, [Inst k v], [[Inst k v]])

mkPointer :: Component k v -> Pointer v
mkPointer (pivot, top, _) = Pointer{ pointerSize = size, pointerPivot = pivot }
  where
    size = length top -- inefficient, improve

-- precondition: top is not empty
mkContent :: Component k v -> Content k v
mkContent (_, top, _) = assert notEmpty Content{ contents = N.fromList top }
  where
    notEmpty = not $ null top

subdivide :: Comparator v -> [Inst k v] -> [[Inst k v]] -> BinTreeU (Component k v)
subdivide f top bottoms = B.unfoldTree (uncurry $ halveNode f) (top, bottoms)

halveNode :: Comparator v -> [Inst k v] -> [[Inst k v]] -> Either (Component k v) (Component k v, ([Inst k v], [[Inst k v]]), ([Inst k v], [[Inst k v]]))
halveNode f top bottoms
  | rightSize == 0 = Left (pivot, top, bottoms)
  | f leftmost rightmost == EQ = Left (pivot, top, bottoms)
  | otherwise = assert (addUp && equalSized) $ Right ((pivot, top, bottoms), (top_lefts, bottom_lefts), (top_rights, bottom_rights))
  where
    -- INEFFICIENT!!! Improve.
    size = length top
    midpos = subtract 1 . ceiling $ size % 2
    pivot = snd $ top !! midpos
    (leftmost, rightmost) = (snd $ head top, snd $ last top)
    split = (/= LT) . f pivot . snd
    (top_lefts, top_rights) = cleaveByPivot f pivot top -- L.partition split top
    (bottom_lefts, bottom_rights) = unzip $ map (cleaveByPivot f pivot) bottoms
    (leftSize, rightSize) = (length top_lefts, length top_rights)
    addUp = length top_lefts + length top_rights == size
    equalSized = and $ map ((length top_lefts ==) . length) bottom_lefts ++ map ((length top_rights ==) . length) bottom_rights

-- | divide list into instances smaller or equal instances and greater instances
cleaveByPivot :: Comparator v -> v -> [Inst k v] -> ([Inst k v], [Inst k v])
cleaveByPivot f pivot = L.partition ((/= LT) . f pivot . snd)

-- precondition: bottoms is non-empty
expandBottom :: [Comparator v] -> (v, [Inst k v], [[Inst k v]]) -> (Pointer v, Nest (Pointer v) (Content k v))
expandBottom _ (_, _, []) = error "bottom may not be empty when expanding"
expandBottom fs (pivot, top, top' : bottoms) = (Pointer{ pointerSize = size, pointerPivot = pivot }, buildMultiRangeTreeWorker fs top' bottoms)
  where
    size = length top -- inefficient, improve

type Query v = (v,v)

-- later: fuse collecting and labeling?
query :: Query v -> MultiRangeTree k v -> [(k,v)]
query q mrt = collectPoints $ checkRange fs q t
  where
    (fs, t) = (comparators &&& getMultiRangeTree) mrt

data Answer = Contained | Overlapping | Disjoint deriving (Show, Eq)

checkRange :: ComparatorSeq v -> Query v -> Nest (Pointer v) (Content k v) -> Nest Answer [(k,v)]
checkRange fs query = flood (adaptFloodCascade checkPointer descend) (checkContent fs) (query, (Nothing, Nothing), Overlapping, fs)
  where
    descend (query, range, ans, f :| fs') _ _ = let
      errorMsg = "number of comparators needs to match tree nesting"
        in (query, (Nothing, Nothing), Overlapping, fromMaybe (error errorMsg) $ N.nonEmpty fs')

adaptFloodCascade :: (a -> b -> (d,a,a)) -> (a -> b -> d -> a) -> a -> b -> (d, a, (a,a))
adaptFloodCascade fshallow fdescend wave x = let
  (x', leftWave, rightWave) = fshallow wave x
  nestWave = fdescend wave x x'
  in (x', nestWave, (leftWave, rightWave))           

type RangeParcel v = (Query v, Range (Maybe v), Answer, ComparatorSeq v)

updRange :: Range (Maybe v) -> RangeParcel v -> RangeParcel v
updRange newRange (query, _, ans, fs') = (query, newRange, ans, fs')

checkPointer :: RangeParcel v -> Pointer v -> (Answer, RangeParcel v, RangeParcel v)
checkPointer parcel@(_, _, Contained, _) ptr = let allRange = (Nothing, Nothing) in (Contained, updRange allRange parcel, updRange allRange parcel)
checkPointer parcel@(_, _, Disjoint, _) ptr = let noRange = (Nothing, Nothing) in (Disjoint, updRange noRange parcel, updRange noRange parcel)
checkPointer parcel@(query, range, Overlapping, fs') ptr = let
  ans = checkQuery (N.head fs') query range
  (leftRange, rightRange) = splitRange (pointerPivot ptr) range
  in (ans, updRange leftRange parcel, updRange rightRange parcel)
  where
    updRange newRange (query, _, ans, fs') = (query, newRange, ans, fs')

checkContent :: ComparatorSeq v -> RangeParcel v -> Content k v -> [(k,v)]
checkContent _ (_, _, Contained, _) con = N.toList $ contents con
checkContent _ (_, _, Disjoint, _) _ = []
checkContent fs (query, range, Overlapping, fs') con = filter allInside . N.toList $ contents con
  where
    allInside (_, point) = all (\f -> inside f query point) fs

-- pre: left <= pivot <= right
splitRange :: v -> Range (Maybe v) -> (Range (Maybe v), Range (Maybe v))
splitRange pivot (left, right) = ((left, Just pivot), (Just pivot, right))

collectPoints :: Nest Answer [(k,v)] -> [(k,v)]
collectPoints = drain addBranch addLeaf
  where
    addBranch _ Nothing Nothing = error "either nest or subs need to be Just"
    addBranch Disjoint _ _ = []
    addBranch Overlapping _ (Just (lefts, rights)) = lefts ++ rights -- inefficient!!!
    addBranch Overlapping (Just nests) Nothing = nests
    addBranch Contained (Just nests) _ = nests
    addBranch Contained Nothing (Just (lefts, rights)) = lefts ++ rights
    addLeaf pts = pts

elimAnswer :: a -> a -> a -> Answer -> a
elimAnswer xc _ _ Contained = xc
elimAnswer _ xo _ Overlapping = xo
elimAnswer _ _ xd Disjoint = xd

inside :: Comparator v -> Query v -> v -> Bool
inside f (lo,hi) p = f lo p /= GT && f hi p /= LT

-- | predicate: query contains range
contains :: Comparator v -> Query v -> Range v -> Bool
contains f (ql,qr) (rl,rr) = f ql rl /= GT && f qr rr /= LT

-- | predicate: query contains range where range may be extend to +/- infinity
containsX :: Comparator v -> Query v -> Range (Maybe v) -> Bool
containsX f q (rl, rr) = maybe False (contains f q) ((,) <$> rl <*> rr)

-- | predicate: query and range are disjoint
disjoint :: Comparator v -> Query v -> Range v -> Bool
disjoint f (ql,qr) (rl,rr) = f ql rr == GT || f qr rl == LT

-- | predicate: query and range are disjoint, where range may extend to +/- infinity
disjointX :: Comparator v -> Query v -> Range (Maybe v) -> Bool
disjointX f q (Just rl, Just rr) = disjoint f q (rl, rr)
disjointX f (ql,qr) (Nothing, Just rr) = f ql rr == GT
disjointX f (ql,qr) (Just rl, Nothing) = f qr rl == LT
disjointX f _ (Nothing, Nothing) = False

-- check how the first range relates to the second range
checkQuery :: (v -> v -> Ordering) -> Query v -> Range (Maybe v) -> Answer
checkQuery fcmp q r
  | containsX fcmp q r = Contained
  | disjointX fcmp q r = Disjoint
  | otherwise = Overlapping

demoMrt :: (MultiRangeTree Int (Int,Int), [(Int,Int) -> (Int,Int) -> Ordering])
demoMrt = let
  ps = [(1,2), (3,4), (9,5), (7,4), (5,5), (8,1)]
  mkf f x y = f x `compare` f y
  fs = [mkf fst, mkf snd]
  in (buildMultiRangeTree (N.fromList fs) (N.fromList . zip [0 ..] $ ps), fs)
