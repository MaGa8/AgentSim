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

import MultiRangeTree

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
  arbitrary = (:|) <$> arbitrary <*> arbitrary
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
  arbitrary = mkPair4List <$> ((:|) <$> arbitrary <*> arbitrary)
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
prop_numberOfElementsRec = testTree (nodeSizes . getMultiRangeTree) (\_ -> fst . drain gatherAndCheck prepLeaf)
  where
    nodeSizes = mapNest pointerSize (N.length . contents)
    prepLeaf n = (True, n)
    gatherAndCheck n nst subs = ( maybe True (\(t,nestn) -> t && n == nestn) nst &&
                                    maybe True (\((lt,leftn), (rt,rightn)) -> lt && rt && n == leftn + rightn) subs
                                , n)

calcNodeMinMax :: Nest (Pointer P3) (Content Int P3) -> Nest (Int, Int) (Int, Int)
calcNodeMinMax = mapWithLevelKey minMaxFromPointer minMaxFromContent accessors
  where
    minMaxFromPointer mf ptr = let f = fromJust mf in bimap f f $ pointerRange ptr
    minMaxFromContent mf con = let f = fromJust mf
                                   ps = contents con
                               in (minimum $ N.map (f . snd) ps, maximum $ N.map (f . snd) ps)

-- problem: does not pick up difference in dim 2
prop_rangesCoverTop :: N.NonEmpty P3 -> Bool
prop_rangesCoverTop = testTree (map (either id id) . roots . calcNodeMinMax . getMultiRangeTree) (\ps minMaxs -> and $ zipWith (==) (dimensionMinMax ps) minMaxs :: Bool)
  where
    dimensionMinMax ps = map (\f -> let mapped = map (f . snd) ps in (minimum mapped, maximum mapped)) accessors

-- top-level range is correct
prop_rangesCoverRec :: N.NonEmpty P3 -> Bool
prop_rangesCoverRec = testTree (evalCoverage . calcNodeMinMax . getMultiRangeTree) (const checkCorrect)
  where
    evalCoverage = fst . newEcho evalBranch (True,)
    evalBranch (l,u) _ subs = maybe (True, (l,u)) (\((ll,lu), (rl,ru)) -> (l == ll && ru == u, (l,u))) subs

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
prop_checkRangesDisjoint = testTree (fst . newEcho checkChildren (True,) . calcNodeMinMax . getMultiRangeTree) (const checkCorrect)
  where
    checkChildren ran _  = (,ran) . maybe True (\((lmin,lmax), (rmin,rmax)) -> lmax <= rmin)

return []
testMultiRangeTree = $quickCheckAll
