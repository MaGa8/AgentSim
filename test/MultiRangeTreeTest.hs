{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module MultiRangeTreeTest
  (
    testMultiRangeTree
  ) where

import Test.QuickCheck

import Debug.Trace

import Data.Bifunctor
import qualified Data.List.NonEmpty as N
import Data.Foldable
import Data.Maybe

import Control.Arrow((&&&))
import Control.Applicative

import MultiRangeTree
import Nest

type P3 = (Int,Int,Int)

fst3,snd3,trd3 :: P3 -> Int
fst3 (x,_,_) = x
snd3 (_,x,_) = x
trd3 (_,_,x) = x

accessors :: [P3 -> Int]
accessors = [fst3, snd3, trd3]

mk :: (Ord b) => (a -> b) -> a -> a -> Ordering
mk f p1 p2 = f p1 `compare` f p2

comparators3 :: [P3 -> P3 -> Ordering]
comparators3 = map mk accessors

instance (Arbitrary a) => Arbitrary (N.NonEmpty a) where
  arbitrary = (N.:|) <$> arbitrary <*> arbitrary
  shrink = mapMaybe N.nonEmpty . shrink . N.toList

type Tree3d = MultiRangeTree Int P3
type Inst = (Int,P3)
newtype TestPair = TestPair ([Inst], MultiRangeTree Int P3)

-- steps of common test:
-- (1) build tree from points 
-- (2) compute with the tree yielding some product
-- (3) compare the tree against the product
testTree :: Testable b => (Tree3d -> a) -> ([Inst] -> a -> b) -> N.NonEmpty P3 -> b
testTree run ver ps = ver (N.toList xs) . run $ buildMultiRangeTree (N.fromList comparators3) xs
  where
    xs :: N.NonEmpty Inst
    xs = N.zip (N.fromList [1 ..]) ps

mkPair4List :: N.NonEmpty P3 -> TestPair
mkPair4List xs = let
  points = N.zip (N.fromList [1 ..]) xs
  in TestPair (N.toList points, buildMultiRangeTree (N.fromList comparators3) points)

instance Arbitrary TestPair where
  arbitrary = mkPair4List <$> ((N.:|) <$> arbitrary <*> arbitrary)
  -- shrink (TestPair (ps,_)) = let
  --   (l,r) = bimap maybeMkPair maybeMkPair . halve $ map snd ps
  --   in maybe [] shrink l ++ maybe [] shrink r
  --   where
  --     maybeMkPair = fmap mkPair4List . N.nonEmpty

halve :: [a] -> ([a],[a])
halve xs = let mid = floor . (/2) . fromIntegral $ length xs in splitAt mid xs

-- total number of elements is correct
prop_numberOfElementsTop :: N.NonEmpty P3 -> Bool
prop_numberOfElementsTop ps = testTree (calcRootSizes . getMultiRangeTree) checkRootSizes ps
  where
    calcRootSizes = map (either (N.length . contents) pointerSize) . roots
    checkRootSizes ps = all (== length ps)
-- weird test cases
-- (-11,11,10) :| []
-- 
  
-- prop_numberOfElementsTop :: TestPair -> Property
-- prop_numberOfElementsTop (TestPair (ps,t)) = within 10 $ all (== length ps) treeSizes
  -- where treeSizes = map (either (N.length . contents) pointerSize) $ roots t

-- number of elements adds up everywhere in the tree
prop_numberOfElementsRec :: N.NonEmpty P3 -> Bool
prop_numberOfElementsRec = testTree numberOfElementsRecCompute (const numberOfElementsRecCheck)

numberOfElementsRecCompute :: Tree3d -> Nest Int Int
numberOfElementsRecCompute = mapNest pointerSize (N.length . contents) . getMultiRangeTree

numberOfElementsRecCheck :: Nest Int Int -> Bool
numberOfElementsRecCheck = fst . drain gatherAndCheck (True,)
  where
    gatherAndCheck n nst subs = ( maybe True (\(t,nestn) -> t && n == nestn) nst &&
                                  maybe True (\((lt,leftn), (rt,rightn)) -> lt && rt && n == leftn + rightn) subs
                                , n)

calcNodeRange :: Nest (Pointer P3) (Content Int P3) -> Nest (Int, Int) (Int, Int)
calcNodeRange = fst . echo calcBranch calcLeaf . labelLevels accessors
  where
    -- echo instances, store ranges at node
    dupl = id &&& id
    calcLeaf (f, con) = let
      insts = N.toList $ snd <$> contents con
      coord = f $ head insts
      in (dupl coord, insts)
    -- either left or right need to be Just
    calcBranch (f, ptr) mbNest mbSubs = let
      insts = fromJust $ fmap (uncurry (++)) mbSubs <|> mbNest
      coords = map f insts
      in ((minimum coords, maximum coords), insts)

-- problem: does not pick up difference in dim 2
prop_rangesCoverTop :: N.NonEmpty P3 -> Bool
prop_rangesCoverTop = testTree rangesCoverTopCompute rangesCoverTopCheck
  where
    dimensionMinMax ps = map (\f -> let mapped = map (f . snd) ps in (minimum mapped, maximum mapped)) accessors

rangesCoverTopCompute :: Tree3d -> [(Int, Int)]
rangesCoverTopCompute  = map (either id id) . roots . calcNodeRange . getMultiRangeTree

rangesCoverTopCheck :: [Inst] -> [(Int, Int)] -> Bool
rangesCoverTopCheck ps ranges = length realRanges == length ranges && and (zipWith (==) realRanges ranges)
  where
    realRanges = zip mins maxs
    coords = [map (f . snd) ps | f <- accessors]
    (mins, maxs) = (map minimum coords, map maximum coords)

rangesCoverRecCompute :: Tree3d -> Nest Bool Bool
rangesCoverRecCompute = evalCoverage . calcNodeRange . getMultiRangeTree
  where
    evalCoverage = fst . echo evalBranch (const (True,Nothing))
    evalBranch (l,u) _ subs = maybe (True, Just (l,u)) (\(leftr,rightr) -> (maybe True ((== l) . fst) leftr && maybe True ((== u) . snd) rightr, Just (l,u))) subs

-- l == ll && ru == u, Just (l,u))) subs

-- top-level range is correct
prop_rangesCoverRec :: N.NonEmpty P3 -> Bool
prop_rangesCoverRec = testTree rangesCoverRecCompute (const checkCorrect)

{-
compareWithSubranges :: (Pointer v -> Maybe (Range v) -> Maybe (Range v,Range v) -> a)
                     -> MultiRangeTree k v -> Nest a ()
compareWithSubranges f = fst . echoFull compareNestBranch compareNestLeaf compareFlatBranch compareFlatLeaf
  where
    compareNestBranch p rn (rl,rr) = (f p (Just rn) (Just (rl,rr)),pointerRange p)
    compareNestLeaf p rn = (f p (Just rn) Nothing,pointerRange p)
    compareFlatBranch p rl rr = (f p Nothing (Just (rl,rr)),pointerRange p)
    compareFlatLeaf c = ((),range $ Left c)

collectChildren :: Nest a b -> Nest (a,Maybe (Either b a),Maybe (Either b a,Either b a)) b
collectChildren = fst . echo collectNest collectSub integrate collectLeaf
  where
    collectLeaf :: b -> (b,Either b a)
    collectLeaf y = (y,Left y)
    collectNest x nv = ((x,Just nv,Nothing),Right x)
    collectSub x lv rv = ((x,Nothing,Just (lv,rv)),Right x)
    integrate (x,nv,_) _ (_,_,sv) _ = ((x,nv,sv),Right x)
-}

checkCorrect :: Nest Bool Bool -> Bool
checkCorrect = drain testInner id
  where testInner t nst subs = t && maybe True (uncurry (&&)) subs && fromMaybe True nst

prop_checkRangesDisjoint :: N.NonEmpty P3 -> Bool
prop_checkRangesDisjoint = testTree (fst . echo checkChildren (True,) . calcNodeRange . getMultiRangeTree) (const checkCorrect)
  where
    checkChildren ran _  = (,ran) . maybe True (\((lmin,lmax), (rmin,rmax)) -> lmax <= rmin)

checkQueryCompute :: P3 -> P3 -> Tree3d -> [Inst]
checkQueryCompute left right = query (left,right)

checkQueryCheck :: P3 -> P3 -> [Inst] -> [Inst] -> Bool
checkQueryCheck left right pop qresult = subsetOf result filtered && subsetOf filtered result
  where
    filtered = filter (insideOf left right) $ map snd pop
    result = map snd qresult

subsetOf :: (Eq a) => [a] -> [a] -> Bool
subsetOf sub super = all (`elem` super) sub

insideOf :: P3 -> P3 -> P3 -> Bool
insideOf (lx,ly,lz) (ux,uy,uz) (x,y,z) = all (\(l,e,u) -> l <= e && e <= u) [(lx,x,ux), (ly,y,uy), (lz,z,uz)]

prop_checkQuery :: P3 -> P3 -> N.NonEmpty P3 -> Bool
prop_checkQuery left right = testTree (checkQueryCompute left right) (checkQueryCheck left right)

return []
testMultiRangeTree = $quickCheckAll
