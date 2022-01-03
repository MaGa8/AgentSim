{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module MultiRangeTree
  (
    NonEmpty(..), (<|)
  , BinTree(..)
  , Nest(..), NTree
  , isFlat, isLeaf, root, roots, children, nest, elimNest
  , floodFull, flood, floodF, drainFull, drain, echoFull, echo, mapNest, zipNest
  -- new functions, destined to replace the other zoo
  , newDrain, newEcho
  , labelNestLevels, prettyPrintNest
  , MultiRangeTree(..), Range, Query, Pointer(..), Content(..)
  , contentValues, contentKeys --, range, mapWithLevelKey
  , Answer(..), elimAnswer
  , contains, disjoint, checkQuery
  , Comparator, ComparatorSeq
  , buildMultiRangeTree, query
  ) where

import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty(NonEmpty(..), (<|))
import qualified Data.List as L
import Data.Bifunctor
import Data.Maybe
import Data.Ratio
import Data.Either
import Data.Foldable as F

import qualified BinTree as B
import BinTree(BinTree(..))

import Control.Applicative
import Control.Monad(when, join)
import Control.Arrow(left,right,(&&&))
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Exception

import Debug.Trace as Dbg

import Rank

type Size = Int
type Height = Int
type Range v = (v,v)

type NestNode a b = (a, Nest a b)

elimNestNode :: (a -> Nest a b -> c) -> NestNode a b -> c
elimNestNode f (x, nst) = f x nst

mkNestNode :: a -> Nest a b -> NestNode a b
mkNestNode = (,)

type NTree a b = BinTree (NestNode a b) (NestNode a b)

rootNTree :: NTree a b -> a
rootNTree = either fst fst . B.root

-- | Wrapper around binary trees that allow for nesting
data Nest a b = Flat (BinTree a b) | Nest (NTree a b) deriving Show -- use GADT to ensure that only branches can be nested

elimNest :: (BinTree a b -> c) -> (NTree a b -> c) -> Nest a b -> c
elimNest f _ (Flat t) = f t
elimNest _ g (Nest t) = g t

mkNest :: Either (BinTree a b) (NTree a b) -> Nest a b
mkNest = either Flat Nest

-- | forces the arguments before applying the functions
(!.) :: (b -> c) -> (a -> b) -> a -> c
(!.) f g x = let y = g x
             in x `seq` y `seq` f y

unfoldNest :: forall a b c d.
  -- | decide at root whether to build a Flat (Left) or a Nest (Right)
  (a -> Either b a) ->
  -- | for Nest: construct value passed to subtree, build value at node and decide whether to build children
  (a -> (c,a,Maybe (a,a))) ->
  -- | for Flat: construct leaf value or construct branch value and values passed to children
  (b -> Either d (c,b,b)) ->
  a -> Nest c d
unfoldNest p fn ff = either (Flat . B.unfoldTree ff) (Nest . B.unfoldTree nestedUnfolding) . p
  where
    nestedUnfolding :: a -> Either (c,Nest c d) ((c,Nest c d),a,a)
    nestedUnfolding s = let
      (v,ns,inner) = fn s
      nst = unfoldNest p fn ff ns
      in maybe (Left (v,nst)) (\(ls,rs) -> Right ((v,nst),ls,rs)) inner

unfoldNest' :: forall a b c d.
  -- | decide at root whether to build a Flat (Left) or a Nest (Right)
  (a -> Either b a) ->
  -- | for Nest: construct value passed to subtree, build value at node and decide whether to build children
  (a -> (c,a,Maybe (a,a))) ->
  -- | for Flat: construct leaf value or construct branch value and values passed to children
  (b -> Either d (c,b,b)) ->
  a -> Nest c d
unfoldNest' p fn ff = either (Flat !. B.unfoldTree' ff) (Nest !. B.unfoldTree' nestedUnfolding) . p
  where
    nestedUnfolding :: a -> Either (c,Nest c d) ((c,Nest c d),a,a)
    nestedUnfolding s = let
      (v,ns,inner) = fn s
      nst = unfoldNest' p fn ff ns
      in v `seq` nst `seq` maybe (Left (v,nst)) (\(ls,rs) -> Right ((v,nst),ls,rs)) inner      

isFlat :: Nest a b -> Bool
isFlat = elimNest (const True) (const False)

isLeaf :: Nest a b -> Bool
isLeaf = elimNest B.isLeaf B.isLeaf

toNest :: Nest a b -> NTree a b
toNest (Nest t) = t

toFlat :: Nest a b -> BinTree a b
toFlat (Flat t) = t

root :: Nest a b -> Either b a
root = elimNest B.root (B.elimTree (\(x,_) _ _ -> Right x) (\(x,_) -> Right x))

rootU :: Nest a a -> a
rootU = either id id . root

roots :: Nest a b -> [Either b a]
roots = drain (\x n _ -> Right x : fromMaybe [] n) (return . Left)

children :: Nest a b -> Maybe (Nest a b, Nest a b)
children = elimNest (fmap (bimap Flat Flat) . B.children) (fmap (bimap Nest Nest) . B.children)

nest :: Nest a b -> Maybe (Nest a b)
nest = elimNest (const Nothing) (either (const Nothing) (Just . snd) . B.root)

floodFull :: forall a b c d e.
             (a -> b -> (d,a,(a,a))) -- ^ at nested branch
          -> (a -> b -> (d,a)) -- ^ at nested leaf
          -> (a -> b -> (d,a,a)) -- ^ at flat branch
          -> (a -> c -> e) -- ^ at flat leaf
          -> a -> Nest b c -> Nest d e
floodFull fnb fnl ffb ffl s = elimNest (Flat . B.flood ffb ffl s) (Nest . B.flood handleNestBranch handleNestLeaf s)
  where
    handleNestBranch :: a -> (b,Nest b c) -> ((d,Nest d e),a,a)
    handleNestBranch s' (x,nst) = let (x',nsts,(ls,rs)) = fnb s' x in ((x',floodFull fnb fnl ffb ffl nsts nst),ls,rs)
    handleNestLeaf :: a -> (b,Nest b c) -> (d,Nest d e)
    handleNestLeaf s' (x,nst) = let (x',nsts) = fnl s' x in (x', floodFull fnb fnl ffb ffl nsts nst)

flood :: (a -> b -> (d,a,(a,a))) -- ^ at any nested node and flat branch ignoring irrelevant output
      -> (a -> c -> e) -- ^ at flat leaf
      -> a -> Nest b c -> Nest d e
flood f = floodFull f (\s x -> let (x',nsts,_) = f s x in (x',nsts)) (\s x -> let (x',_,(ls,rs)) = f s x in (x',ls,rs))

-- variant of flood where the wave to the nested tree and the wave to the subtrees are determined independently
floodF :: forall a b c d e.
          (a -> b -> (d,a)) -- ^ produce inner value from wave
       -> (a -> a) -- ^ wave to nested tree
       -> (a -> (a,a)) -- ^ wave to subtrees
       -> (a -> c -> e) -- ^ produce leaf value from wave
       -> a -> Nest b c -> Nest d e
floodF fb fnst fsub = floodFull floodNestBranch floodNestLeaf floodFlatBranch
  where
    floodNestBranch w v = let (v',w') = fb w v in (v',fnst w',fsub w')
    floodNestLeaf w v = let (v',w') = fb w v in (v',fnst w')
    floodFlatBranch w v = let (v',w') = fb w v in uncurry (v',,) $ fsub w'

-- what about a monadic variant of flood?
-- use case: carry list of comparators; need: access head function and pop the head before recursing into nested tree
-- Need different monadic environments for nested tree, left and right subtree. Each is tied to the monadic value of the originating node.
-- Since the monadic value is split we can use the separated interface of floodF
{-
floodM :: forall a b c d e m.
          (a -> b -> m (d,a)) -- ^ produce inner value from wave
       -> (a -> m a) -- ^ wave to nested tree
       -> (a -> (m a, m a)) -- ^ wave to subtrees
       -> (a -> c -> e) -- ^ produce leaf value from wave
       -> a -> Nest b c -> m (Nest d e)
floodM fb fnst fsub fl x t = elimNest () () t
-}

newDrain :: (a -> Maybe c -> Maybe (c,c) -> c) -> (b -> c) -> Nest a b -> c
newDrain fb fl = elimNest (B.drain fbFlat fl) (B.drain fbNest flNest . B.mapTree reduceNest reduceNest)
  where
    fbFlat x left right = fb x Nothing (Just (left, right))
    fbNest (x,nst) left right = fb x (Just nst) (Just (left, right))
    flNest (x,nst) = fb x (Just nst) Nothing
    reduceNest = elimNestNode (\x nst -> (x, newDrain fb fl nst))

drainFull :: forall a b c d.
             (a -> Either c d -> (d,d) -> d) -- ^ eliminate nested branch
          -> (a -> Either c d -> d) -- ^ eliminate nested leaf
          -> (a -> c -> c -> c) -- ^ eliminate flat branch
          -> (b -> c) -- ^ eliminate leaf of flat tree
          -> Nest a b -> Either c d
drainFull fnb fnl ffb ffl = elimNest (Left . B.drain ffb ffl) (Right . B.drain handleNestBranch handleNestLeaf)
  where
    handleNestBranch :: (a,Nest a b) -> d -> d -> d
    handleNestBranch (x,nst) cl cr = fnb x (drainFull fnb fnl ffb ffl nst) (cl,cr)
    handleNestLeaf :: (a,Nest a b) -> d
    handleNestLeaf (x,nst) = fnl x (drainFull fnb fnl ffb ffl nst)

drain :: forall a b c.
         (a -> Maybe c -> Maybe (c,c) -> c) -- ^ eliminate a nested branch, nested leaf or flat branch
      -> (b -> c)  -- ^ eliminate flat leaf
      -> Nest a b -> c
drain f g = either id id . drainFull fnb fnl ffb g
  where
    fnb :: a -> Either c c -> (c,c) -> c
    fnb x cnst csub = f x (either Just Just cnst) (Just csub)
    fnl :: a -> Either c c -> c
    fnl x cnst = f x (either Just Just cnst) Nothing
    ffb :: a -> c -> c -> c
    ffb x cl cr = f x Nothing $ Just (cl,cr)

recaseDrainer :: (a -> b -> (b,b) -> c) -> (a -> b -> c) -> (a -> (b,b) -> c) -> a -> Maybe b -> Maybe (b,b) -> c
recaseDrainer nestedBranch _ _ x (Just nst) (Just pair) = nestedBranch x nst pair
recaseDrainer _ nestedLeaf _ x (Just nst) Nothing = nestedLeaf x nst
recaseDrainer _ _ flatBranch x Nothing (Just pair) = flatBranch x pair

adaptFlatBranch :: (a -> Maybe b -> Maybe (b,b) -> c) -> a -> b -> b -> c
adaptFlatBranch f x l r = f x Nothing (Just (l,r))

newEcho :: forall a b c d e. (a -> Maybe e -> Maybe (e,e) -> (c,e))
        -> (b -> (d,e))
        -> Nest a b -> (Nest c d, e)
newEcho fb fl = elimNest (first Flat . B.echo (adaptFlatBranch fb) fl) (first Nest . B.echo handleNestBranch handleNestLeaf)
  where
    handleNestBranch :: (a, Nest a b) -> e -> e -> ((c, Nest c d), e)
    handleNestBranch (x,nst) le re = let (nst', nste) = newEcho fb fl nst in first (,nst') $ fb x (Just nste) (Just (le,re))
    handleNestLeaf :: (a, Nest a b) -> ((c, Nest c d), e)
    handleNestLeaf (x,nst) = let (nst', nste) = newEcho fb fl nst in first (,nst') $ fb x (Just nste) Nothing


echoFull :: (a -> e -> (e,e) -> (c,e)) -- ^ echo for nested inner node
         -> (a -> e -> (c,e)) -- ^ echo for nested leaf
         -> (a -> e -> e -> (c,e)) -- ^ echo for flat inner node
         -> (b -> (d,e)) -- ^ echo for flat leaf
         -> Nest a b -> (Nest c d,e)
echoFull fnb fnl ffb ffl = either id id . drainFull echoNestBranch echoNestLeaf echoFlatBranch echoFlatLeaf
  where
    echoNestBranch x nst ((l,el),(r,er)) = let (n,e) = either id id nst
                                           in first (\x' -> Nest $ Branch (x',n) (toNest l) (toNest r)) $ fnb x e (el,er)
    echoNestLeaf x nst = let (n,e) = either id id nst in first (\x' -> Nest $ Leaf (x',n)) $ fnl x e
    echoFlatBranch x (l,el) (r,er) = first (\x' -> Flat $ Branch x' (toFlat l) (toFlat r)) $ ffb x el er
    echoFlatLeaf y = first (Flat . Leaf) $ ffl y

-- first combine echo from subtrees then combine echo from nested tree
echo :: (a -> e -> (c,e)) -- ^ combine value and echo from nested tree
     -> (a -> e -> e -> (c,e)) -- ^ combine value and echoes from subtrees
     -> (c -> e -> c -> e -> (c,e)) -- ^ integrate product from nested tree and from subtree subtrees
     -> (b -> (d,e))
     -> Nest a b -> (Nest c d, e)
echo fnest fsub fint = echoFull echoNestBranch fnest fsub
  where
    echoNestBranch x en (el,er) = let (nx,ne) = fnest x en
                                      (sx,se) = fsub x el er
                                  in fint nx ne sx se

mapNest :: (a -> c) -> (b -> d) -> Nest a b -> Nest c d
mapNest f g = elimNest (Flat . B.mapTree f g) (Nest . B.mapTree mapNestBranch (bimap f (mapNest f g)))
  where
    mapNestBranch = bimap f (mapNest f g)

-- | zip two topologically identical trees together
zipTree :: (a -> c -> e) -> (b -> d -> f) -> BinTree a b -> BinTree c d -> Maybe (BinTree e f)
zipTree f g (Leaf x) (Leaf y) = Just . Leaf $ g x y
zipTree f g (Branch x xl xr) (Branch y yl yr) = Branch (f x y) <$> zipTree f g xl yl <*> zipTree f g xr yr
zipTree _ _ _ _ = Nothing

zipTreeM :: Monad m => (a -> c -> m e) -> (b -> d -> m f) -> BinTree a b -> BinTree c d -> MaybeT m (BinTree e f)
zipTreeM f g (Leaf x) (Leaf y) = fmap Leaf . lift $ g x y
zipTreeM f g (Branch x xl xr) (Branch y yl yr) = Branch <$> lift (f x y) <*> zipTreeM f g xl yl <*> zipTreeM f g xr yr
zipTreeM f g _ _ = MaybeT . return $ Nothing

zipNest :: (a -> c -> e) -> (b -> d -> f) -> Nest a b -> Nest c d -> Maybe (Nest e f)
zipNest f g (Flat t) (Flat u) = Flat <$> zipTree f g t u
zipNest f g (Nest t) (Nest u) = do
  values <- zipTree f f (B.mapTree fst fst t) (B.mapTree fst fst u)
  nests <- join . runMaybeT $ zipTreeM (zipNest f g) (zipNest f g) (B.mapTree snd snd t) (B.mapTree snd snd u)
  Nest <$> zipTree (,) (,) values nests

type PadShow = String -> IO ()

labelNestLevels :: Nest a b -> Nest (a,Int) (b,Int)
labelNestLevels = flood labelBranch labelLeaf 0
  where
    labelBranch n x = ((x,n),n+1,(n,n))
    labelLeaf n x = (x,n)

prettyPrintNest :: forall a b. (Show a,Show b) => Maybe Int -> Nest a b -> IO ()
prettyPrintNest maxd = either ($ "") ($ "") . drainFull printNestBranch printNestLeaf printFlatBranch printFlatLeaf . labelNestLevels
  where
    printValuePadded x pad = putStrLn $ pad ++ show x
    -- accumulated value is String -> IO () where String argument is the padding to be applied to every line
    printNestBranch :: (a,Int) -> Either PadShow PadShow -> (PadShow,PadShow) -> String -> IO ()
    printNestBranch (x,n) nstio (lio,rio) pad = do
      printValuePadded x pad
      when (maybe True (n <) maxd) $ either ($ pad ++ "^^") ($ pad ++ "^^") nstio >> putStrLn ""
      lio $ pad ++ "Nl "
      rio $ pad ++ "Nr "
    printNestLeaf :: (a,Int) -> Either PadShow PadShow -> String -> IO ()
    printNestLeaf (x,n) nstio pad = do
      printValuePadded x pad
      when (maybe True (n <) maxd) $ either ($ pad ++ "^^") ($ pad ++ "^^") nstio >> putStrLn ""
    printFlatBranch :: (a,Int) -> PadShow -> PadShow -> String -> IO ()
    printFlatBranch (x,_) lio rio pad = do
      printValuePadded x pad
      lio (pad ++ "Fl ")
      rio (pad ++ "Fr ")
    printFlatLeaf :: (b,Int) -> String -> IO ()
    printFlatLeaf (x,_) = printValuePadded x


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
    -- noneEmpty = and $ map (not . null) [top_lefts, top_rights] ++ map (not . null) [bottom_lefts, bottom_rights]
    addUp = length top_lefts + length top_rights == size
    equalSized = and $ map ((length top_lefts ==) . length) bottom_lefts ++ map ((length top_rights ==) . length) bottom_rights

-- | divide list into instances smaller or equal instances and greater instances
cleaveByPivot :: Comparator v -> v -> [Inst k v] -> ([Inst k v], [Inst k v])
cleaveByPivot f pivot = L.partition ((/= LT) . f pivot . snd)

nestTree :: (a -> (b, Nest b c)) -> BinTreeU a -> NTree b c
nestTree f = B.mapTree f f

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

-- | first flood top level then descend to the nested trees
floodCascade :: (a -> b -> (d, a, a)) -> (a -> c -> e) -> (a -> b -> d -> a) -> a -> Nest b c -> Nest d e
floodCascade floodBranch floodLeaf floodDesc wave = elimNest (Flat . B.flood floodBranch floodLeaf wave) (Nest . B.flood floodNestBranch floodNestLeaf wave)
  where
    floodNestBranch wave' (x, nst) = let (y, waveLeft, waveRight) = floodBranch wave' x
                                     in ((y, floodCascade floodBranch floodLeaf floodDesc (floodDesc wave' x y) nst), waveLeft, waveRight)
    floodNestLeaf wave' (x, nst) = let (y, _, _) = floodBranch wave' x
                                   in (y, floodCascade floodBranch floodLeaf floodDesc (floodDesc wave' x y) nst)

data Answer = Contained | Overlapping | Disjoint deriving (Show, Eq)

checkRange :: ComparatorSeq v -> Query v -> Nest (Pointer v) (Content k v) -> Nest Answer [(k,v)]
checkRange fs query = floodCascade checkPointer (checkContent fs) descend (query, (Nothing, Nothing), Overlapping, fs)
  where
    descend (query, range, ans, f :| fs') _ _ = (query, range, ans, fromMaybe (error "") $ N.nonEmpty fs')

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
collectPoints = newDrain addBranch addLeaf
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

{-
mapWithLevelKey :: (Maybe l -> a -> c) -> (Maybe l -> b -> d) -> [l] -> Nest a b -> Nest c d
mapWithLevelKey fb fl = floodF mapBranch splitNest (id &&& id) mapLeaf
  where
    mapBranch cmps' = (,cmps') . fb (fst <$> L.uncons cmps')
    splitNest = maybe [] snd . L.uncons
    mapLeaf cmps' = fl (fst <$> L.uncons cmps')

organize :: Comparator v -> NonEmpty (k,v) -> Either (Content k v) (NonEmpty (k,v), NonEmpty (k,v))
organize fcmp xs
  | null ls = Left . Content $ N.fromList rs
  | null rs = Left . Content $ N.fromList ls
  | otherwise = Right (N.fromList ls, N.fromList rs)
  where
    (_,ls,rs) = fromJust . approxPartitionByMedian (cmpBySnd fcmp) $ N.toList xs

buildMultiRangeTree' :: ComparatorSeq v -> NonEmpty (k,v) -> MultiRangeTree k v
buildMultiRangeTree' (f :| fs) points = MultiRangeTree{ comparators = f :| fs, getMultiRangeTree = buildMultiRangeTreeWorker (f : fs) (top, bottoms, ptr) }
  where
    top = L.sortBy (cmpBySnd f) $ N.toList points
    bottoms = map (\f' -> L.sortBy (cmpBySnd f') $ N.toList points) fs
    ptr = Pointer{ pointerSize = N.length points, pointerHeight = -1, pointerRange = sorted2range top }

-- more efficient with Sequence?
sorted2range :: [(k,v)] -> (v,v)
sorted2range points = (snd $ head points, snd $ last points)

type RangeNest k v = Nest (Pointer v) (Content k v)
type RangeFlat k v = BinTree (Pointer v) (Content k v)
type Component k v = ([(k,v)], [[(k,v)]], Pointer v)
type Subdivision k v = BinTree (Component k v) (Component k v)

-- precondition: list of comparators and list of points are non-empty
buildMultiRangeTreeWorker :: [Comparator v] -> Component k v -> RangeNest k v
buildMultiRangeTreeWorker [f] c = Flat . B.mapTree component2pointer component2content $ subdivide f c
buildMultiRangeTreeWorker (f : fs) c = Nest . nestTree (expandPointers fs) $ subdivide f c

component2pointer :: Component k v -> Pointer v
component2pointer (_, _, ptr) = ptr

-- get empty component on input [(0,0,0), (0,0,0)]. Why?
component2content :: Component k v -> Content k v
component2content (pts, _, _) = Content{ contents = N.fromList pts }

nestTree :: (a -> (b, Nest b c)) -> BinTree a a -> NTree b c
nestTree f = B.mapTree f f

-- Precondition: bottom of component may not be empty
expandPointers :: [Comparator v] -> Component k v -> (Pointer v, RangeNest k v)
expandPointers fs (top, newtop : bottoms, ptr) = (ptr, buildMultiRangeTreeWorker fs newcomp)
  where
    newcomp = (newtop, bottoms, ptr{ pointerRange = (snd $ head newtop, snd $ last newtop) }) -- get range more efficiently?
    -- idea: keep range of first bottom in component
  
subdivide :: Comparator v -> Component k v -> Subdivision k v
subdivide f = B.unfoldTree (\comp -> second (uncurry (comp,,)) $ halveComponent f comp)

-- diagnosis: bottoms are partitioned by value but top is partitioned by position
-- in the presence of non-unique values there is a mismatch between tops and bottoms passed to left and right (possibly resulting in empty lists)
-- proposed fix: all lesser&equal values go left, all greater values go right for both tops and bottoms
halveComponent :: Comparator v -> Component k v -> Either (Component k v) (Component k v, Component k v)
halveComponent f comp@(top, bottoms, ptr)
  | uncurry f (pointerRange ptr) == EQ = Left comp
  | leftSize == 0 || rightSize == 0 = Left comp
  | otherwise = Right ((leftTop, leftBottoms, leftPtr), (rightTop, rightBottoms, rightPtr))
  where    
    (leftTop, leftSize, leftRange, rightTop, rightSize, rightRange, median) = splitMiddle f (pointerSize ptr) (pointerRange ptr) top
    (leftBottoms, rightBottoms) = foldr' (\(l,r) -> bimap (l :) (r :)) ([], []) $ map (partitionAgainst f median) bottoms
    (leftPtr, rightPtr) = ( Pointer{ pointerRange = leftRange, pointerSize = leftSize, pointerHeight = -1 } -- don't use pointerHeight!
                          , Pointer{ pointerRange = rightRange, pointerSize = rightSize, pointerHeight = -1 })

-- !!! ISSUE WAS HERE
splitMiddle :: Comparator v -> Int -> (v,v) -> [(k,v)] -> ([(k,v)], Int, (v,v), [(k,v)], Int, (v,v), v)
splitMiddle f size (lower, upper) points = (leftVals, leftSize, (lower, lowerMedian), rightVals, rightSize, (upperMedian, upper), lowerMedian)
  where
    midpos = floor (size % 2)
    -- inefficient: fuse later
    upperMedian = snd $ points !! midpos
    (leftVals, rightVals) = L.partition ((== GT) . f upperMedian . snd) points
    lowerMedian = maybe lower (snd . fst) . L.uncons $ reverse leftVals
    (leftSize, rightSize) = (length leftVals, length rightVals)

    -- (leftSize, rightSize) = (floor (size % 2), size - leftSize)
    -- (leftHalf, rightHalf) = splitAt leftSize points
    -- median = snd $ head rightHalf

partitionAgainst :: Comparator v -> v -> [(k,v)] -> ([(k,v)], [(k,v)])
partitionAgainst f piv = L.partition ((== GT) . f piv . snd)


buildMultiRangeTree :: ComparatorSeq v -> NonEmpty (k,v) -> MultiRangeTree k v
buildMultiRangeTree fs = buildPointers fs . distribute fs

-- distributes points in nested tree by splitting by the median
distribute :: forall k v. NonEmpty (v -> v -> Ordering) -> NonEmpty (k,v) -> Nest () (Content k v)
distribute fs xs = unfoldNest decideNesting nestUnfold flatUnfold (fs,xs)
  where
    decideNesting :: (ComparatorSeq v, NonEmpty (k,v)) -> Either (Comparator v, NonEmpty (k,v)) (ComparatorSeq v, NonEmpty (k,v))
    decideNesting a@(fcmp :| [],xs') = Left (fcmp,xs')
    decideNesting a = Right a
    nestUnfold :: (ComparatorSeq v,NonEmpty (k,v))
               -> ((),(ComparatorSeq v,NonEmpty (k,v)),Maybe ((ComparatorSeq v,NonEmpty (k,v)),(ComparatorSeq v,NonEmpty (k,v))))
    nestUnfold (fs',xs') = let
      nsta = (N.fromList $ N.tail fs',xs')
      in either (const ((),nsta,Nothing)) (\(ls,rs) -> ((),nsta,Just ((fs',ls),(fs',rs)))) $ organize (N.head fs') xs'
    flatUnfold :: (Comparator v, NonEmpty (k,v))
               -> Either (Content k v) ((),(Comparator v,NonEmpty (k,v)),(Comparator v,NonEmpty (k,v)))
    flatUnfold (f,xs') = do
      (ls,rs) <- organize f xs'
      return ((),(f,ls),(f,rs))

mergePointers :: Pointer v -> Pointer v -> Pointer v
mergePointers pl pr = Pointer{ pointerHeight = 1 + max (pointerHeight pl) (pointerHeight pr)
                             , pointerSize = pointerSize pl + pointerSize pr
                             , pointerRange = (fst $ pointerRange pl, snd $ pointerRange pr) }

merge2Pointer :: Either (Content k v) (Pointer v) -> Either (Content k v) (Pointer v) -> Pointer v
merge2Pointer pl pr = mergePointers (toPointer pl) (toPointer pr)

type SRT k v = BinTree (Pointer v) (Content k v) -- simple range tree
type MRT k v = NTree (Pointer v) (Content k v) -- multi range tree (raw type)

toPointer :: Either (Content k v) (Pointer v) -> Pointer v
toPointer = either con2ptr id
  where con2ptr c = Pointer{ pointerRange = let v = snd. N.head $ contents c in (v,v)
                           , pointerSize = N.length $ contents c
                           , pointerHeight = 0 }

buildPointers :: forall k v. ComparatorSeq v -> Nest () (Content k v) -> MultiRangeTree k v
buildPointers cmps@(fcmp :| fs) = MultiRangeTree cmps . either Flat Nest . drainFull (const mkNestInner) (const mkNestLeaf) (const mkFlatInner) mkLeaf
  where
    mkNestInner :: Either (SRT k v) (MRT k v) -> (MRT k v,MRT k v) -> MRT k v
    mkNestInner nt (lt,rt) = B.Branch (mergePointers (rootNTree lt) (rootNTree rt),either Flat Nest nt) lt rt
    mkNestLeaf :: Either (SRT k v) (MRT k v) -> MRT k v
    mkNestLeaf nt = B.Leaf (toPointer $ either B.root (Right . rootNTree) nt, mkNest nt)
    mkFlatInner :: SRT k v -> SRT k v -> SRT k v
    mkFlatInner lt rt = B.Branch (merge2Pointer (B.root lt) (B.root rt)) lt rt
    mkLeaf :: Content k v -> SRT k v
    mkLeaf = B.Leaf

data Answer = Contained | Overlapping | Disjoint deriving (Show, Eq)

elimAnswer :: a -> a -> a -> Answer -> a
elimAnswer xc _ _ Contained = xc
elimAnswer _ xo _ Overlapping = xo
elimAnswer _ _ xd Disjoint = xd

contains :: Comparator v -> Query v -> Range v -> Bool
contains fcmp (ql,qr) (rl,rr) = ql `fcmp` rl /= GT && qr `fcmp` rr /= LT

overlap :: Comparator v -> Query v -> Range v -> Bool
overlap fcmp (ql,qr) (rl,rr) = ql `fcmp` rl /= LT && ql `fcmp` rr /= GT || rl `fcmp` ql /= LT && rl `fcmp` qr /= GT

-- check how the first range relates to the second range
checkQuery :: (v -> v -> Ordering) -> Query v -> Range v -> Answer
checkQuery fcmp q r
  | contains fcmp q r = Contained
  | overlap fcmp q r = Overlapping
  | otherwise = Disjoint

type Query v = (v,v)

-- check result of query conditioned on earlier answer
checkSuccQuery :: (v -> v -> Ordering) -> Answer -> Query v -> Range v -> Answer
checkSuccQuery _ Contained _ _ = Contained
checkSuccQuery _ Disjoint _ _ = Disjoint
checkSuccQuery cmp Overlapping q r = checkQuery cmp q r

labelRangeContained :: [v -> v -> Ordering] -> Query v -> MultiRangeTree k v -> Nest (Pointer v,Answer) (Content k v,Bool)
labelRangeContained fs q = floodF prodB splitNest splitSub prodL (Overlapping,fs) . getMultiRangeTree
  where
    prodB (_,[]) p = ((p,Contained),(Contained,[]))
    prodB (a,fs'@(cmp : _)) p = let
      a' = checkSuccQuery cmp a q $ pointerRange p
      in ((p,a'),(a',fs'))
    prodL (_,[]) c = (c,True)
    prodL (a,cmp : fs') c = (c,checkSuccQuery cmp a q (range $ Left c) == Contained)
    splitNest (Contained,fs') = maybe (Contained,[]) ((Overlapping,) . snd) $ L.uncons fs'
    splitNest (a,fs') = maybe (Contained,[]) ((demote4Nest a,) . snd) $ L.uncons fs'
    demote4Nest = elimAnswer Overlapping Overlapping Disjoint
    splitSub (a,fs') = ((a,fs'),(a,fs'))

query :: [v -> v -> Ordering] -> Query v -> MultiRangeTree k v -> [(k,v)]
query fs q = drain collectInner collectLeaf . labelRangeContained fs q
  where
    collectInner :: (Pointer v,Answer) -> Maybe [(k,v)] -> Maybe ([(k,v)],[(k,v)]) -> [(k,v)]
    collectInner (_,Disjoint) _ _ = []
    -- either nest or subtrees need to be Just values
    collectInner (_,Contained) nstxs subxs = fromJust $ nstxs <|> fmap (uncurry (++)) subxs
    collectInner (_,Overlapping) nstxs subxs = fromJust $ fmap (uncurry (++)) subxs <|> nstxs
    collectLeaf (c,t) = if t then N.toList $ N.zip (contentKeys c) (contentValues c) else []
-}

demoMrt :: (MultiRangeTree Int (Int,Int), [(Int,Int) -> (Int,Int) -> Ordering])
demoMrt = let
  ps = [(1,2), (3,4), (9,5), (7,4), (5,5), (8,1)]
  mkf f x y = f x `compare` f y
  fs = [mkf fst, mkf snd]
  in (buildMultiRangeTree (N.fromList fs) (N.fromList . zip [0 ..] $ ps), fs)
