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
import Data.Sequence(ViewL(..), ViewR(..), (><))
import qualified Data.Sequence as S
import qualified Data.DList as D
import Data.Bifunctor
import Data.Maybe
import Data.Ratio
import Data.Foldable as F

import qualified BinTree as B
import BinTree(BinTree(..))

import Control.Applicative
import Control.Arrow((&&&), (|||))
import Control.Exception

import Debug.Trace as Dbg

import Rank
import Nest

type Size = Int
type Range v = (v,v)
type OpenRange v = Range (Maybe v)

mkRange :: v -> v -> Range v
mkRange lower upper = (lower, upper)

unbounded :: Range (Maybe v)
unbounded = (Nothing, Nothing)

leftOpen :: v -> Range (Maybe v)
leftOpen upper = (Nothing, Just upper)

rightOpen :: v -> Range (Maybe v)
rightOpen lower = (Just lower, Nothing)

-- pre: lower <= mid <= upper
divide :: v -> Range v -> (Range v, Range v)
divide mid (lower, upper) = (mkRange lower mid, mkRange mid upper)

-- pre: lower1 <= lower 2 and upper1 <= upper 2
unite :: Range v -> Range v -> Range v
unite (lower1, upper1) (lower2, upper2) = (lower1, upper2)

-- pre: lower < upper
vacate :: Range v -> Range v
vacate (lower, upper) = mkRange upper lower

isEmpty :: Comparator v -> Range v -> Bool
isEmpty f (lower, upper) = f lower upper == GT

data Pointer a = Pointer{ pointerSize :: Size -- ^ number of points assigned to subtree
                        , pointerPivot :: !a -- ^ greatest value in the left subtree
                        , pointerRange :: OpenRange a
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

instkey :: Inst k v -> k
instkey = fst

instval :: Inst k v -> v
instval = snd

cmpBySnd f (_,x) (_,y) = f x y

buildMultiRangeTree :: ComparatorSeq v -> NonEmpty (Inst k v) -> MultiRangeTree k v
buildMultiRangeTree (f :| fs) points = MultiRangeTree{ comparators = f :| fs, getMultiRangeTree = buildMultiRangeTreeWorker (f : fs) size top bottoms }
  where
    size = length points
    top = L.sortBy (cmpBySnd f) $ N.toList points
    bottoms = map (\f' -> L.sortBy (cmpBySnd f') $ N.toList points) fs

buildMultiRangeTreeWorker :: [Comparator v] -> Size -> [Inst k v] -> [[Inst k v]] -> Nest (Pointer v) (Content k v)
buildMultiRangeTreeWorker [f] n !top [] = Flat . B.mapTree mkPointer mkContent $ subdivide f n unbounded (S.fromList top) []
buildMultiRangeTreeWorker _ _ _ [] = error "Bottoms can't be empty while there's > 1 comparator."
buildMultiRangeTreeWorker (f : fs) n !top bottoms = Nest . nestTree (expandBottom fs) $ subdivide f n unbounded (S.fromList top) bottoms

type BinTreeU a = BinTree a a

type Component k v = (v, Size, OpenRange v, S.Seq (Inst k v), [[Inst k v]])

mkPointer :: Component k v -> Pointer v
mkPointer (pivot, size, range, top, _) = Pointer{ pointerSize = size, pointerPivot = pivot, pointerRange = range }

-- precondition: top is not empty
mkContent :: Component k v -> Content k v
mkContent (_, _, _, top, _) = assert notEmpty Content{ contents = N.fromList $ F.toList top }
  where
    notEmpty = not $ null top

subdivide :: Comparator v -> Size -> OpenRange v -> S.Seq (Inst k v) -> [[Inst k v]] -> BinTreeU (Component k v)
subdivide f size range top bottoms = B.unfoldTree (\(size', range', top', bottoms') -> measureNode size' range' top' bottoms' >> halveNode f size' range' top' bottoms') (size, range, top, bottoms)

measureNode :: Size -> OpenRange v -> S.Seq (Inst k v) -> [[Inst k v]] -> Either (Component k v) ()
measureNode _ _ S.Empty _ = error "node without points was erroneously created while constructing the tree"
measureNode _ range top@(point S.:<| S.Empty) bottom = let coord = instval point in Left (instval point, 1, (Just coord, Just coord), top, bottom) -- make point range
measureNode size _ top bottom = Right ()

-- pre: size >= 2
-- pre: top is sorted
-- post: order within lists persists
halveNode :: Comparator v -> Size -> OpenRange v -> S.Seq (Inst k v) -> [[Inst k v]]
          -> Either (Component k v) (Component k v, (Size, OpenRange v, S.Seq (Inst k v), [[Inst k v]]), (Size, OpenRange v, S.Seq (Inst k v), [[Inst k v]]))
halveNode f size range top bottom
  -- make point range as all points are equal
  | cmpBySnd f leftmost rightmost == EQ = let
      point = instval leftmost
      pointRange = (Just point, Just point)
      in assert (size >= 2) $ Left (instval leftmost, size, pointRange, top, bottom) 
  | otherwise = let
      (pivot, (leftSize, topLefts), (rightSize, topRights)) = mkEvenChunks f size top
      comp = (pivot, size, range, top, bottom)
      (bottomLefts, bottomRights) = unzip $ map (cleaveByPivot f pivot) bottom
      (leftRange, rightRange) = divide (Just pivot) range
      left = (leftSize, leftRange, topLefts, bottomLefts)
      right = (rightSize, rightRange, topRights, bottomRights)
      equalSized = equalSizedTopBottom topLefts bottomLefts && equalSizedTopBottom topRights bottomRights
      in assert equalSized Right (comp, left, right)
  where
    midpos = subtract 1 . ceiling $ size % 2
    (leftmost :< _, _ :> rightmost) = S.viewl &&& S.viewr $ top

equalSizedTopBottom :: (Foldable t1, Foldable t2) => t1 a -> [t2 a] -> Bool
equalSizedTopBottom top = all ((length top ==) . length)

-- | divide list into instances smaller or equal instances and greater instances
cleaveByPivot :: Comparator v -> v -> [Inst k v] -> ([Inst k v], [Inst k v])
cleaveByPivot f pivot = L.partition ((/= LT) . f pivot . snd)
-- cleaveByPivot f pivot = foldr' categorize ([], [])
--   where
--     categorize pt (los, his) = case f pivot (snd pt) of
--                                  LT -> (los, pt : his)
--                                  _ -> (pt : los, his)

type Chunk k v = (Size, [Inst k v])

type ChunkS k v = (Size, S.Seq (Inst k v))

-- pre: head pts < last pts
mkEvenChunks :: Comparator v -> Size -> S.Seq (Inst k v) -> (v, ChunkS k v, ChunkS k v)
mkEvenChunks f size pts
  -- special case: pivot does not divide
  | cmpBySnd f leftEnd rightEnd == EQ = let
      (leftChunkSize, rightChunkSize) = (halfSize - length leftEquals, size - leftChunkSize)
      left = (leftChunkSize, leftLessers)
      right = (rightChunkSize, leftEquals >< rightHalf)
      sizesAddUp = leftChunkSize + rightChunkSize == size
      in assert sizesAddUp (instval leftEqualsEnd, left, right)
  | otherwise = let
      (leftChunkSize, rightChunkSize) = (halfSize + length rightEquals, size - leftChunkSize)
      left = (leftChunkSize, leftHalf >< rightEquals)
      right = (rightChunkSize, rightGreaters)
      sizesAddUp = leftChunkSize + rightChunkSize == size
      in assert sizesAddUp (instval leftEnd, left, right)
  where
    halfSize = lowerMedianRank size + 1
    (begin :< _, _ :> end) = (S.viewl &&& S.viewr) pts
    (leftHalf, rightHalf) = assert (cmpBySnd f begin end == LT) S.splitAt halfSize pts
    (_ :> leftEnd, _ :> rightEnd) = (S.viewr leftHalf, S.viewr rightHalf)
    (rightEquals, rightGreaters) = S.spanl ((== EQ) . cmpBySnd f leftEnd) rightHalf
    (leftEquals, leftLessers) = S.spanr ((== EQ) . cmpBySnd f leftEnd) leftHalf
    (_ :> leftEqualsEnd) = S.viewr leftLessers

emptyChunk :: Chunk k v
emptyChunk = (0, [])

chunkByPivot :: Comparator v -> v -> [Inst k v] -> (Chunk k v, Chunk k v)
chunkByPivot f pivot = foldr' (\x chunks -> move chunks x . f pivot $ snd x) (emptyChunk, emptyChunk)
  where
    move (left, (size, right)) x LT = (left, (size + 1, x : right))
    move ((size, left), right) x _ = ((size + 1, x : left), right)

-- precondition: bottoms is non-empty
expandBottom :: [Comparator v] -> Component k v -> (Pointer v, Nest (Pointer v) (Content k v))
expandBottom _ (_, _, _, _,[]) = error "bottom may not be empty when expanding"
expandBottom fs (pivot, size, range, top, top' : bottoms) = (Pointer{ pointerSize = size, pointerPivot = pivot, pointerRange = range }, buildMultiRangeTreeWorker fs size top' bottoms)

type Query v = (v,v)

query = queryVisitr

queryVisitr :: Query v -> MultiRangeTree k v -> [(k,v)]
queryVisitr q mrt = visitr chooseNestBranch chooseNestLeaf chooseFlatBranch collectBranch collectLeaf [] (False, fs) $ getMultiRangeTree mrt
  where
    fs = N.toList $ comparators mrt
    -- typical problem: cannot tell if we are in a Nest or a Flat -> choice of subtrees depends on this!
    chooseNestBranch (_, []) _ = error "ran out of comparators"
    chooseNestBranch (True, _ : fs') _ = (accept fs', (decline, decline))
    chooseNestBranch (False, f : fs') ptr = case checkQuery f q $ pointerRange ptr of
      Contained -> (moveOn fs', (decline, decline))
      Disjoint -> (decline, (decline, decline))
      Overlapping -> (decline, (moveOn $ f : fs', moveOn $ f : fs'))
    chooseNestLeaf (_, []) _ = error "ran out of comparators"
    chooseNestLeaf (True, _ : fs') ptr = moveOn fs'
    chooseNestLeaf (_, f : fs') ptr = case checkQuery f q (pointerRange ptr) of
      Contained -> moveOn fs'
      _ -> decline -- comparison on point range can either be contained or disjoint
    chooseFlatBranch (_, []) _ = error "ran out of comparators"
    chooseFlatBranch (True, fs') ptr = (accept fs', accept fs')
    chooseFlatBranch (False, fs') ptr = case checkQuery (head fs') q (pointerRange ptr) of
      Contained -> (accept fs', accept fs')
      Disjoint -> (decline, decline)
      Overlapping -> (moveOn fs', moveOn fs')
    collectBranch pts _ _ = pts
    collectLeaf _ (_, []) con = error "ran out of comparators at leaf"
    collectLeaf pts (True, _) con = N.toList (contents con) ++ pts
    collectLeaf pts (False, f : _) con = filter (inside f q . instval) (N.toList $ contents con) ++ pts
    accept fs' = const $ Just (True, fs')
    moveOn fs' = const $ Just (False, fs')
    decline = const Nothing


queryFold :: Query v -> MultiRangeTree k v -> [(k,v)]
queryFold q mrt = collectRanges . cutDisjoint $ markRanges fs q t
  where
    (fs, t) = (comparators mrt, getMultiRangeTree mrt)

type Marker v = Maybe (Answer, [Comparator v], OpenRange v)

-- Compute result depending on marker.  Recalculate only in the Overlapping case.
procMarker :: a -> ([Comparator v] -> OpenRange v -> a) -> ([Comparator v] -> OpenRange v -> a) -> Query v -> Marker v -> a
procMarker  valDisjoint _ _ _ Nothing = valDisjoint
procMarker _ fContained _ _ (Just (Contained, fs, ran)) = fContained fs ran
procMarker valDisjoint fContained fOverlap q (Just (Overlapping, fs, ran)) = case checkQuery (head fs) q ran of
  Disjoint -> valDisjoint
  Contained -> fContained fs ran
  Overlapping -> fOverlap fs ran

lowerMarker :: [Comparator v] -> Marker v
lowerMarker (_ : fs) = Just (Overlapping, fs, unbounded)

-- split ranges if the range is overlapping
splitMarker :: [Comparator v] -> OpenRange v -> Pointer v -> (Marker v, Marker v)
splitMarker fs ran ptr = let
  (leftRange, rightRange) = divide (Just $ pointerPivot ptr) ran
  in (Just (Overlapping, fs, leftRange), Just (Overlapping, fs, rightRange))

-- send the same range if the range is contained
relayMarker :: [Comparator v] -> OpenRange v -> (Marker v, Marker v)
relayMarker fs ran = (Just (Contained, fs, ran), Just (Contained, fs, ran))

narrowMarker :: Maybe v -> Marker v -> Marker v
narrowMarker p = fmap (\(ans, fs, _) -> (ans, fs, (p,p)))

-- this function eats nearly 60% of total time!
markRanges :: ComparatorSeq v -> Query v -> Nest (Pointer v) (Content k v) -> Nest Bool [(k,v)]
markRanges fs q = floodFull markInnerNest markLeafNest markInnerFlat markLeafFlat $ Just (Overlapping, N.toList fs, unbounded)
  where
    markInnerNest mark ptr = procMarker (False, Nothing, (Nothing, Nothing)) (\fs' _ -> (True, lowerMarker fs', (Nothing, Nothing))) (\fs' ran -> (True, Nothing, splitMarker fs' ran ptr)) q mark
    -- markInnerNest mark@(ans, fs', range, need) ptr = let
    --   ans' = calcAnswer fs' ans q range
    --   (leftRange, rightRange) = divide (Just $ pointerPivot ptr) range
    --   in ( need && ans' /= Disjoint -- collect if it is not disjoint and needed by parent
    --      , lowerMarker (need && ans' == Contained) mark -- collect if contained
    --      , (turnMarker ans' leftRange (need && ans' == Overlapping) mark, turnMarker ans' rightRange (need && ans' == Overlapping) mark) -- collect if overlapping
    --      )
    -- leaf holds identical values -> tighten check
    markLeafNest mark ptr = procMarker (False, Nothing) (\fs' _ -> (True, lowerMarker fs')) (\fs' ran -> (True, lowerMarker fs')) q $ narrowMarker (Just $ pointerPivot ptr) mark
    -- markLeafNest mark@(ans, fs', range, need) ptr = let
    --   piv = pointerPivot ptr
    --   ans' = calcAnswer fs' ans q (Just piv, Just piv) -- leaf holds identical values -> tighten check
    --   in ( need && ans' == Contained    -- point value may not be overlapping
    --      , lowerMarker (need && ans' == Contained) mark
    --      )
    markInnerFlat mark ptr = let
      disjointValue = (False, Nothing, Nothing)
      fcontained fs' ran = let mark' = Just (Contained, fs', ran) in (True, mark', mark')
      foverlap fs' ran = uncurry (True,,) $ splitMarker fs' ran  ptr
      in procMarker disjointValue fcontained foverlap q mark
    -- markInnerFlat mark@(ans, fs', range, need) ptr = let
    --   ans' = calcAnswer fs' ans q range
    --   (leftRange, rightRange) = divide (Just $ pointerPivot ptr) range
    --   in ( need && ans' /= Disjoint
    --      , turnMarker ans' leftRange (need && ans' /= Disjoint) mark
    --      , turnMarker ans' rightRange (need && ans' /= Disjoint) mark
    --      )
    markLeafFlat mark con = procMarker [] (\_ _ -> N.toList $ contents con) (\fs' _ -> filter (inside (head fs') q . snd) . N.toList $ contents con) q mark
    -- markLeafFlat (ans, fs', range, True) con = case calcAnswer fs' ans q range of
    --   Disjoint -> []
    --   Contained -> N.toList $ contents con
    --   Overlapping -> filter (inside (head fs') q . snd) . N.toList $ contents con
    -- markLeafFlat (_, _, _, False) _ = []

-- | pre: list of comparators is not empty
calcAnswer :: [Comparator v] -> Answer -> Query v -> OpenRange v -> Answer
calcAnswer _ Contained _ _ = Contained
calcAnswer _ Disjoint _ _ = Disjoint
calcAnswer (f : fs) Overlapping q range = checkQuery f q range

-- | removes that are disjoint from the query
cutDisjoint :: Nest Bool [(k,v)] -> Nest Bool [(k,v)]
cutDisjoint = trim cutNest cutFlat
  where
    cutNest False _ _ = Just False
    cutNest True _ _ = Nothing
    cutFlat False _ _ = Just []
    cutFlat True _ _ = Nothing

-- | collects all lists
collectRanges :: Nest a [(k,v)] -> [(k,v)]
collectRanges = foldr' collect [] . NestU . mapNest Left Right
  where
    collect val pts = either (const pts) (++ pts) val

type CheckPack v = (Answer, Range (Maybe v), [Comparator v])

-- problem: on query ((1,2), (8,5)) does not exclude (9,5). Why?
queryFuse :: Query v -> MultiRangeTree k v -> [(k,v)]
queryFuse q mrt = F.toList $ visit (checkInnerPointer q) (checkLeafPointer q) collectBranch (\pack con -> selectLeaf q pack con) (Overlapping, unbounded, fs) t
  where
    (!t, !fs) = (getMultiRangeTree &&& (N.toList . comparators)) mrt

debugCheckRangePointer :: Show v => Query v -> CheckPack v -> Pointer v -> ((), Maybe (CheckPack v), (Maybe (CheckPack v), Maybe (CheckPack v)))
debugCheckRangePointer q pack@(ans, range, _) ptr = Dbg.trace packStr $ checkRangePointer q pack ptr
  where
    packStr = "query " ++ show q ++ " range " ++ show range ++ " is " ++ show ans ++ " split " ++ show (pointerPivot ptr) ++ "\n"

-- pre: list of comparators is not empty
checkRangePointer :: Query v -> CheckPack v -> Pointer v -> ((), Maybe (CheckPack v), (Maybe (CheckPack v), Maybe (CheckPack v)))
checkRangePointer _ (_, _, []) _ = error "ran out of comparators when checking range"
checkRangePointer _ (Disjoint, _, _) _ = error "passed Disjoint on to branch"  -- disjoint => no need to visit further
-- cannot go deeper if there are no more comparators
checkRangePointer _ (Contained, range, [f]) ptr = ((), Nothing, let
                                                      (leftRange, rightRange) = divide (Just $ pointerPivot ptr) range
                                                      in (Just (Contained, leftRange, [f]), Just (Contained, rightRange, [f])))
checkRangePointer _ (Contained, range, fs) _ = ((), Just (Overlapping, unbounded, tail fs), (Nothing, Nothing)) -- contained => go to nest
checkRangePointer q (Overlapping, range, fs) ptr = case checkQuery (head fs) q range of
  Disjoint -> ((), Nothing, (Nothing, Nothing))
  Contained -> ((), Just (Overlapping, unbounded, tail fs), (Nothing, Nothing))
  -- PROBLEM: if this is a leaf we go to nest without checking the current coordinate for this subtree!
  -- solution: need to filter on collection
  Overlapping -> ((), Just (Overlapping, unbounded, tail fs), let
                     (leftRange, rightRange) = divide (Just $ pointerPivot ptr) range
                     in (Just (Overlapping, leftRange, fs), Just (Overlapping, rightRange, fs)))

checkInnerPointer :: Query v -> CheckPack v -> Pointer v -> (Answer, Maybe (CheckPack v), (Maybe (CheckPack v), Maybe (CheckPack v)))
checkInnerPointer _ (_, _, []) _ = error "ran out of comparators while checking branch"
checkInnerPointer q (ans, range, fs@(f : fs')) ptr
  | ans == Disjoint = disjointResult
  | ans == Contained = containedResult
  | ans' == Disjoint = disjointResult
  | ans' == Contained = containedResult
  | otherwise = (Overlapping, Nothing, (Just (Overlapping, leftRange, fs), Just (Overlapping, rightRange, fs)))
  where
    ans' = checkQuery f q range
    (leftRange, rightRange) = divide (Just $ pointerPivot ptr) range
    disjointResult = (Disjoint, Nothing, (Nothing, Nothing))
    containedResult = (Contained, Just (Overlapping, unbounded, fs'), (Just (Contained, leftRange, fs), Just (Contained, rightRange, fs)))

checkLeafPointer :: Query v -> CheckPack v -> Pointer v -> (Answer, Maybe (CheckPack v))
checkLeafPointer _ (_, _, []) _ = error "ran out of comparators while checking leaf"
checkLeafPointer q (ans, range, f : fs) ptr
  | ans == Disjoint = disjointResult
  | ans == Contained = containedResult
  | ans' == Disjoint = disjointResult
  | ans' == Contained = containedResult
  | otherwise = error "point cannot be Overlapping"
  where
    -- we're at a leaf so every value kept is equal to piv w.r.t f
    ans' = let piv = pointerPivot ptr in checkQuery f q (Just piv, Just piv)
    disjointResult = (Disjoint, Nothing)
    containedResult = (Contained, Just (Overlapping, unbounded, fs))

pickQueryPath :: Answer -> Range (Maybe v) -> v -> N.NonEmpty (Comparator v) -> (Answer, Maybe (CheckPack v), (Maybe (CheckPack v), Maybe (CheckPack v)))
pickQueryPath Disjoint _ _ _ = (Disjoint, Nothing, (Nothing, Nothing))
pickQueryPath ans range piv fs@(_ :| fs') = (ans, Just (Overlapping, range, fs'), let
                                                      (leftRange, rightRange) = divide (Just piv) range
                                                      in (Just (ans, leftRange, N.toList fs), Just (ans, rightRange, N.toList fs)))

-- pre: left == right == Nothing \/ left = Just _ /\ right = Just _
-- collectBranch :: Answer -> Maybe [(k,v)] -> [(k,v)] -> (Maybe [(k,v)], Maybe [(k,v)]) -> [(k,v)]
collectBranch :: Answer -> Maybe (S.Seq (k,v)) -> (Maybe (S.Seq (k,v)), Maybe (S.Seq (k,v))) -> S.Seq (k,v)
-- either collect from subtrees or alternatively collect from nest
collectBranch Disjoint _ _ = S.empty
collectBranch Contained (Just nest) _ = nest
collectBranch Contained _ (Just left, Just right) = left >< right
collectBranch Overlapping _ (Just left, Just right) = left >< right
collectBranch Overlapping (Just nest) _  = nest
collectBranch _ _ _ = error "no visitor values returned even though the answer is not Disjoint"

selectLeaf :: Query v -> CheckPack v -> Content k v -> S.Seq (k,v)
selectLeaf _ (_, _, []) _ = error "ran out of comparators when checking leaf"
selectLeaf _ (Disjoint, _, _) _ = error "passed Disjoint on to leaf"
selectLeaf _ (Contained, _, _) con = S.fromList . N.toList $ contents con
selectLeaf q (Overlapping, _, f : _) con = S.fromList . filter (\(_, pt) -> contains f q (pt, pt)) . N.toList $ contents con

-- later: fuse collecting and labeling?
-- REMOVAL PENDING
queryOld :: Query v -> MultiRangeTree k v -> [(k,v)]
queryOld q mrt = collectPoints $ checkRange fs q t
  where
    (fs, t) = (comparators &&& getMultiRangeTree) mrt

data Answer = Contained | Overlapping | Disjoint deriving (Show, Eq)

-- when flooding make sure parts of the tree are forced!
-- If the root is contained then the remainder of the tree needs to be evaluated
-- If the root is not contained then nothing needs to be forced at all
-- alternatively: try replacing separate check and collect methods by a monolithic version of query
-- such a monolithic version only needs to traverse the shared MRT and does not build a new one for each query!
checkRange :: ComparatorSeq v -> Query v -> Nest (Pointer v) (Content k v) -> Nest Answer [(k,v)]
checkRange fs query = flood (adaptFloodCascade checkPointer descend) (checkContent fs) (query, (Nothing, Nothing), Overlapping, fs)
  where
    descend (!query, !range, !ans, f :| fs') _ _ = let
      errorMsg = "number of comparators needs to match tree nesting"
        in (query, (Nothing, Nothing), Overlapping, fromMaybe (error errorMsg) $ N.nonEmpty fs')

adaptFloodCascade :: (a -> b -> (d,a,a)) -> (a -> b -> d -> a) -> a -> b -> (d, a, (a,a))
adaptFloodCascade fshallow fdescend wave x = let
  (x', leftWave, rightWave) = fshallow wave x
  nestWave = fdescend wave x x'
  in (x', nestWave, (leftWave, rightWave))           

type RangeParcel v = (Query v, Range (Maybe v), Answer, ComparatorSeq v)

updRange :: Range (Maybe v) -> RangeParcel v -> RangeParcel v
updRange newRange (query, _, !ans, fs') = (query, newRange, ans, fs')

checkPointer :: RangeParcel v -> Pointer v -> (Answer, RangeParcel v, RangeParcel v)
checkPointer parcel@(_, _, Contained, _) ptr = let allRange = (Nothing, Nothing) in (Contained, updRange allRange parcel, updRange allRange parcel)
checkPointer parcel@(_, _, Disjoint, _) ptr = let noRange = (Nothing, Nothing) in (Disjoint, updRange noRange parcel, updRange noRange parcel)
checkPointer parcel@(!query, !range, Overlapping, !fs') ptr = let
  !ans = checkQuery (N.head fs') query range
  (!leftRange, !rightRange) = splitRange (pointerPivot ptr) range
  in (ans, updRange leftRange parcel, updRange rightRange parcel)

checkContent :: ComparatorSeq v -> RangeParcel v -> Content k v -> [(k,v)]
checkContent _ (_, _, Contained, _) con = N.toList $ contents con
checkContent _ (_, _, Disjoint, _) _ = []
checkContent fs (!query, !range, Overlapping, fs') con = filter allInside . N.toList $ contents con
  where
    allInside (_, !point) = all (\f -> inside f query point) fs

-- pre: left <= pivot <= right
splitRange :: v -> Range (Maybe v) -> (Range (Maybe v), Range (Maybe v))
splitRange pivot (left, right) = ((left, Just pivot), (Just pivot, right))

-- check if this is really slower
collectPoints_old :: Nest Answer [(k,v)] -> [(k,v)]
collectPoints_old = drain addBranch addLeaf
  where
    addBranch _ Nothing Nothing = error "either nest or subs need to be Just"
    addBranch Disjoint _ _ = []
    addBranch Overlapping _ (Just (lefts, rights)) = lefts ++ rights -- inefficient!!!
    addBranch Overlapping (Just nests) Nothing = nests
    addBranch Contained (Just nests) _ = nests
    addBranch Contained Nothing (Just (lefts, rights)) = lefts ++ rights
    addLeaf pts = pts

collectPoints :: Nest Answer [(k,v)] -> [(k,v)]
collectPoints = D.toList . drain addBranch addLeaf
  where
    addBranch _ Nothing Nothing = error "either nest or subs need to be Just"
    addBranch Disjoint _ _ = D.empty
    addBranch Overlapping _ (Just (lefts, rights)) = D.append lefts rights -- inefficient!!!
    addBranch Overlapping (Just nests) Nothing = nests
    addBranch Contained (Just nests) _ = nests
    addBranch Contained Nothing (Just (lefts, rights)) = D.append lefts rights
    addLeaf pts = D.fromList pts

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
checkQuery !fcmp !q !r
  | containsX fcmp q r = Contained
  | disjointX fcmp q r = Disjoint
  | otherwise = Overlapping

demoMrt :: (MultiRangeTree Int (Int,Int), [(Int,Int) -> (Int,Int) -> Ordering])
demoMrt = let
  ps = [(1,2), (3,4), (9,5), (7,4), (5,5), (8,1)]
  mkf f x y = f x `compare` f y
  fs = [mkf fst, mkf snd]
  in (buildMultiRangeTree (N.fromList fs) (N.fromList . zip [0 ..] $ ps), fs)
