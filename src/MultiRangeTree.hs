{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MultiRangeTree
  (

  ) where

import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty(NonEmpty(..), (<|))
import qualified Data.List as L
import Data.Bifunctor
import Data.Maybe
import Data.Ratio

import qualified BinTree as B
import BinTree(BinTree)

import Control.Applicative
import Control.Monad(when)
import Control.Arrow(left,right)

type Size = Int
type Height = Int
type Range v = (v,v)

type NTree a b = BinTree (a,Nest a b) (Nest a b)

adaptSub :: Either (BinTree a b) (NTree a b) -> NTree a b
adaptSub = either (B.Leaf . Flat) id

-- | Wrapper around binary trees that allow for nesting
data Nest a b = Flat (BinTree a b) | Nest (NTree a b) deriving Show -- use GADT to ensure that only branches can be nested

elimNest :: (BinTree a b -> c) -> (NTree a b -> c) -> Nest a b -> c
elimNest f _ (Flat t) = f t
elimNest _ g (Nest t) = g t

mkNest :: Either (BinTree a b) (NTree a b) -> Nest a b
mkNest = either Flat Nest

unfoldNest :: forall a b c.
  (a -> Either a a) ->
  (a -> (a,Maybe (b,a,a))) ->
  (a -> Either c (b,a,a)) ->
  a -> Nest b c
unfoldNest f g h = either (Flat . B.unfoldTree h) (Nest . B.unfoldTree nestedUnfolding) . f
  where
    nestedUnfolding :: a -> Either (Nest b c) ((b,Nest b c),a,a)
    nestedUnfolding s = let
      (ns,inner) = g s
      nst = unfoldNest f g h ns
      in maybe (Left nst) (\(x,ls,rs) -> Right ((x,nst),ls,rs)) inner

root :: Nest a b -> Either b a
root = elimNest B.root (B.elimTree (\(x,_) _ _ -> Right x) root)

children :: Nest a b -> Maybe (Nest a b, Nest a b)
children = elimNest (fmap (bimap Flat Flat) . B.children) (fmap (bimap Nest Nest) . B.children)

nest :: Nest a b -> Maybe (Nest a b)
nest = elimNest (const Nothing) (either (const Nothing) (Just . snd) . B.root)

mapNest :: (a -> c) -> (b -> d) -> Nest a b -> Nest c d
mapNest f g = elimNest (Flat . B.mapTree f g) (Nest . B.mapTree mapNestBranch (mapNest f g))
  where
    mapNestBranch = bimap f (mapNest f g)

floodFull :: forall a b c d e. (a -> b -> (d,a,(a,a))) -- ^ at nested branch
          -> (a -> b -> (d,a,a)) -- ^ at flat branch
          -> (a -> c -> e) -- ^ at flat leaf
          -> a -> Nest b c -> Nest d e
floodFull fnb ffb ffl s = elimNest (Flat . B.flood ffb ffl s) (Nest . B.flood handleNestBranch handleNestLeaf s)
  where
    handleNestBranch :: a -> (b,Nest b c) -> ((d,Nest d e),a,a)
    handleNestBranch s' (x,nst) = let (x',nsts,(ls,rs)) = fnb s' x in ((x',floodFull fnb ffb ffl nsts nst),ls,rs)
    handleNestLeaf :: a -> Nest b c -> Nest d e
    handleNestLeaf s' nst = floodFull fnb ffb ffl s' nst

flood :: (a -> b -> (d,a,(a,a))) -- ^ at any nested node and flat branch ignoring irrelevant output
          -> (a -> c -> e) -- ^ at flat leaf
          -> a -> Nest b c -> Nest d e
flood f = floodFull f (\s x -> let (x',_,(ls,rs)) = f s x in (x',ls,rs))

drainFull :: forall a b c d.
             (a -> Either c d -> (Either c d,Either c d) -> d) -- ^ eliminate nested branch
          -> (a -> c -> c -> c) -- ^ eliminate flat branch
          -> (b -> c) -- ^ eliminate leaf of flat tree
          -> Nest a b -> Either c d
drainFull fnb ffb ffl = elimNest (Left . B.drain ffb ffl) (B.drain handleNestBranch (drainFull fnb ffb ffl))
  where
    handleNestBranch :: (a,Nest a b) -> Either c d -> Either c d -> Either c d
    handleNestBranch (x,nst) cl cr = Right $ fnb x (drainFull fnb ffb ffl nst) (cl,cr)

drain :: forall a b c.
         (a -> Maybe c -> (c,c) -> c) -- ^ eliminate a nested branch or a flat branch
      -> (b -> c)  -- ^ eliminate flat leaf
      -> Nest a b -> c
drain f g = either id id . drainFull fnb ffb g
  where
    fnb :: a -> Either c c -> (Either c c,Either c c) -> c
    fnb x cnst csub = f x (either Just Just cnst) (bimap (either id id) (either id id) csub)
    ffb :: a -> c -> c -> c
    ffb x cl cr = f x Nothing (cl,cr)

truncFull :: forall a b. 
             (a -> Bool) -- ^ if true transform nested branch into leaf
          -> (a -> Maybe b) -- ^ decide whether to transform flat branch into leaf
          -> Nest a b -> Nest a b
truncFull f g = either Flat Nest . drainFull handleNestBranch handleFlatBranch B.Leaf
  where
    handleNestBranch :: a -> Either (BinTree a b) (NTree a b) -> (Either (BinTree a b) (NTree a b),Either (BinTree a b) (NTree a b)) -> NTree a b
    handleNestBranch x nt (l,r) = if f x then B.Leaf $ mkNest nt else B.Branch (x,mkNest nt) (adaptSub l) (adaptSub r)
    handleFlatBranch :: a -> BinTree a b -> BinTree a b -> BinTree a b
    handleFlatBranch x l r = maybe (B.Branch x l r) B.Leaf $ g x

type PadShow = String -> IO ()

labelNestLevels :: Nest a b -> Nest (a,Int) (b,Int)
labelNestLevels = flood labelBranch labelLeaf 0
  where
    labelBranch n x = ((x,n),n+1,(n,n))
    labelLeaf n x = (x,n)

prettyPrintNest :: forall a b. (Show a,Show b) => Maybe Int -> Nest a b -> IO ()
prettyPrintNest maxd = either ($ "") ($ "") . drainFull printNest printFlatBranch printFlatLeaf . labelNestLevels
  where
    printValuePadded x pad = putStrLn $ pad ++ show x
    -- accumulated value is String -> IO () where String argument is the padding to be applied to every line
    printNest :: (a,Int) -> Either PadShow PadShow -> (Either PadShow PadShow,Either PadShow PadShow) -> String -> IO ()
    printNest (x,n) nstio (lio,rio) pad = do
      printValuePadded x pad
      -- putStrLn $ pad ++ L.replicate (80 - length pad) '*'
      when (maybe True (n <) maxd) $ either ($ pad ++ "^^") ($ pad ++ "^^") nstio
      putStrLn ""
      -- putStrLn $ pad ++ L.replicate (80 - length pad) '*'      
      either ($ pad ++ "Nl") ($ pad ++ "Nl") lio
      either ($ pad ++ "Nr") ($ pad ++ "Nr") rio
    printFlatBranch :: (a,Int) -> PadShow -> PadShow -> String -> IO ()
    printFlatBranch (x,_) lio rio pad = do
      printValuePadded x pad
      lio (pad ++ "Fl")
      rio (pad ++ "Fr")
    printFlatLeaf :: (b,Int) -> String -> IO ()
    printFlatLeaf (x,_) = printValuePadded x
      
  

data Pointer a = Pointer{ pointerHeight :: Height, pointerSize :: Size, pointerRange :: (a,a) } deriving Show
data Content k v = Content{ contentValue :: v, contentKeys :: [k] } deriving Show

type MultiRangeTree k v = Nest (Pointer v) (Content k v)

-- partitions by the (lower) median value not counting multiplicities
partitionByMedian :: (a -> a -> Ordering) -> [a] -> Maybe (a,[a],[a])
partitionByMedian fcmp xs = makePartition <$> medianOfMedians fcmp n medr 5 xs
  where
    n = length xs
    medr = floor $ n % 2
    makePartition med = let (ls,rs) = partitionByPivot fcmp med xs in (med,ls,rs)

partitionByPivot :: (a -> a -> Ordering) -> a -> [a] -> ([a],[a])
partitionByPivot fcmp p = L.partition ((/= LT) . fcmp p)

-- 5 median-of-medians algorithm
medianOfMedians :: (a -> a -> Ordering) -> Int -> Int -> Int -> [a] -> Maybe a
medianOfMedians _ _ _ _ [] = Nothing
medianOfMedians _ _ _ _ [x] = Just x
-- medianOfMedians fcmp _ _ [x,y] = Just $ if fcmp x y == LT then 
medianOfMedians fcmp n i c xs
  | n <= c = Just $ L.sortBy fcmp xs !! (i-1)
  | po == i = Just pivot
  | po > i = medianOfMedians fcmp (n - nu) i c ls
  | po < i = medianOfMedians fcmp (n - nl) (i - nl) c us
  where 
    pivot = fromJust $ medianOfMedians fcmp n' d c centers
    columns = groupsOfN c xs
    centers = map (\xs -> xs !! floor (length xs % 2)) columns
    n' = ceiling $ n % c
    d = floor $ n' % 2
    (ls,us) = partitionByPivot fcmp pivot xs
    po = sum $ map (\x -> if fcmp pivot x == LT then 0 else 1) xs
    (nl,nu) = (length ls,length us)

groupsOfN :: Int -> [a] -> [[a]]
groupsOfN n xs = g : if null xs' then [] else groupsOfN n xs'
  where (g,xs') = splitAt n xs

cmpBySnd f (_,x) (_,y) = f x y

type Comparator a = a -> a -> Ordering
type ComparatorSeq a = NonEmpty (Comparator a)

organize :: Comparator v -> NonEmpty (k,v) -> Either (Content k v) (NonEmpty (k,v), NonEmpty (k,v))
organize fcmp xs
  | null ls = Left Content{ contentValue = snd $ head rs, contentKeys = map fst rs }
  | null rs = Left Content{ contentValue = snd $ head ls, contentKeys = map fst ls }
  | otherwise = Right (N.fromList ls, N.fromList rs)
  where
    (_,ls,rs) = fromJust . partitionByMedian (cmpBySnd fcmp) $ N.toList xs

buildMultiRangeTree :: ComparatorSeq v -> NonEmpty (k,v) -> MultiRangeTree k v
buildMultiRangeTree fs = buildPointers fs . distribute fs

-- demo :: MultiRangeTree Int (Int,Int)
demo :: Nest () (Content Int (Int,Int))
demo = let
  mkf f x y = f x `compare` f y
  ps = N.fromList $ zip [1 ..] [(1,3), (2,5), (7,2), (8,6), (9,9), (5,4)]
  -- in buildMultiRangeTree (N.fromList [mkf fst,mkf snd]) ps
  in distribute (N.fromList [mkf fst,mkf snd]) ps

-- distributes points in nested tree by splitting by the median
distribute :: forall k v. NonEmpty (v -> v -> Ordering) -> NonEmpty (k,v) -> Nest () (Content k v)
distribute fs xs = unfoldNest decideNesting nestUnfold flatUnfold (fs,xs)
  where
    decideNesting :: (ComparatorSeq v, NonEmpty (k,v)) -> Either (ComparatorSeq v, NonEmpty (k,v)) (ComparatorSeq v, NonEmpty (k,v))
    decideNesting a@(fcmp :| [],xs') = Left a
    decideNesting a = Right a
    nestUnfold :: (ComparatorSeq v,NonEmpty (k,v))
               -> ((ComparatorSeq v,NonEmpty (k,v)),Maybe ((),(ComparatorSeq v,NonEmpty (k,v)),(ComparatorSeq v,NonEmpty (k,v))))
    nestUnfold (fs',xs') = let
      nsta = (N.fromList $ N.tail fs',xs')
      in either (const (nsta,Nothing)) (\(ls,rs) -> (nsta,Just ((),(fs',ls),(fs',rs)))) $ organize (N.head fs') xs'
    flatUnfold :: (ComparatorSeq v, NonEmpty (k,v))
               -> Either (Content k v) ((),(ComparatorSeq v,NonEmpty (k,v)),(ComparatorSeq v,NonEmpty (k,v)))
    flatUnfold (fs',xs') = do
      (ls,rs) <- organize (N.head fs') xs'
      return ((),(fs',ls),(fs',rs))

mergePointers :: Pointer v -> Pointer v -> Pointer v
mergePointers pl pr = Pointer{ pointerHeight = 1 + max (pointerHeight pl) (pointerHeight pr)
                             , pointerSize = pointerSize pl + pointerSize pr
                             , pointerRange = (fst $ pointerRange pl, snd $ pointerRange pr) }

merge2Pointer :: Either (Content k v) (Pointer v) -> Either (Content k v) (Pointer v) -> Pointer v
merge2Pointer pl pr = mergePointers (toPointer pl) (toPointer pr)
  where toPointer = either (\con -> Pointer{ pointerHeight = 1, pointerSize = 1, pointerRange = let v = contentValue con in (v,v) } ) id

type SRT k v = BinTree (Pointer v) (Content k v) -- simple range tree
type MRT k v = NTree (Pointer v) (Content k v) -- multi range tree (raw type)

buildPointers :: forall k v. ComparatorSeq v -> Nest () (Content k v) -> MultiRangeTree k v
buildPointers (fcmp :| fs) = either Flat Nest . drainFull (const mkNestInner) (const mkFlatInner) mkLeaf
  where
    mkNestInner :: Either (SRT k v) (MRT k v) -> (Either (SRT k v) (MRT k v),Either (SRT k v) (MRT k v)) -> MRT k v
    mkNestInner nt (lt,rt) = B.Branch (merge2Pointer (root $ mkNest lt) (root $ mkNest rt),either Flat Nest nt) (adaptSub lt) (adaptSub rt)
    mkFlatInner :: SRT k v -> SRT k v -> SRT k v
    mkFlatInner lt rt = B.Branch (merge2Pointer (B.root lt) (B.root rt)) lt rt
    mkLeaf :: Content k v -> SRT k v
    mkLeaf = B.Leaf

{-
data Rangerel = Containing | Overlapping | Disjoint deriving (Show, Eq)

contains :: (v -> v -> Ordering) -> (v,v) -> (v,v) -> Bool
contains fcmp (l1,r1) (l2,r2) = l1 `fcmp` l2 /= GT && r1 `fcmp` r2 /= LT

overlap :: (v -> v -> Ordering) -> (v,v) -> (v,v) -> Bool
overlap fcmp (l1,r1) (l2,r2) = (l1 `fcmp` l2 /= LT && l1 `fcmp` r2 /= GT) || (l2 `fcmp` l1 /= LT && l2 `fcmp` r1 /= GT)

checkRangeRel :: (v -> v -> Ordering) -> (v,v) -> (v,v) -> Rangerel
checkRangeRel fcmp b1 b2
  | contains fcmp b1 b2 = Containing
  | overlap fcmp b1 b2 = Overlapping
  | otherwise = Disjoint

-- problem at leaf: even though some points are the same for one coordinate they may not be for otherwise
-- -> leaves should contain nested trees too s.t. we can compare the other coordinates at leaves too
-- want: NTree a b = Nest (BinTree (a,NTree a b) (a,NTree a b)) | Flat (BinTree a b) cause it's sufficient to treat nested leaves as interior nodes
query :: [v -> v -> Ordering] -> (v,v) -> MultiRangeTree k v -> [(k,v)]
query fs bds = either id id . drain collectNest collectFlat collectLeaf collectLeaf . flood markNest markFlat markLeaf fs
  where
    markLeaf [] con = zip (contentKeys con) (repeat $ contentValue con)
    markLeaf (fcmp : _) con = if overlap fcmp bds (contentValue con,contentValue con) then markLeaf [] con else []
    markFlat [] _ = (Overlapping,[],[])
    markFlat fs' ptr = (checkRangeRel (head fs') bds $ pointerRange ptr,fs',fs')
    markNest [] _ = (Overlapping,[],([],[]))
    markNest fs' ptr = (checkRangeRel (head fs') bds $ pointerRange ptr,tail fs',(fs',fs'))
    collectLeaf = id
    collectFlat Disjoint _ _ = []
    collectFlat _ ls rs = ls ++ rs
    collectNest Disjoint _ _ = []
    collectNest Overlapping _ (ls,rs) = ls ++ rs
    collectNest Containing ns _ = either id id ns 
-}
