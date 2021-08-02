module MultiRangeTree
  (

  ) where

import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty(NonEmpty(..), (<|))
import Data.Bifunctor

import qualified BinTree as B
import BinTree(BinTree)

import Control.Arrow

type Size = Int
type Height = Int
type Range v = (v,v)

type NTree a b = BinTree (a, Nest a b) b

-- | Wrapper around binary trees that allow for nesting
data Nest a b = Flat (BinTree a b) | Nest (NTree a b)

elimNest :: (BinTree a b -> c) -> (NTree a b -> c) -> Nest a b -> c
elimNest f _ (Flat t) = f t
elimNest _ g (Nest t) = g t

unfoldNest ::
  -- | decide whether to build a flat or a nested tree
  (a -> Either (BinTree b c) a) ->
  -- | unfold a nested tree into either a leaf or a nested branch node
  (a -> Either c (b,a,(a,a))) ->
  a -> Nest b c
unfoldNest f g = either Flat (Nest . unfoldNestedTree f g) . f

unfoldNestedTree :: (a -> Either (BinTree b c) a) -> (a -> Either c (b,a,(a,a))) -> a -> BinTree (b, Nest b c) c
unfoldNestedTree f g = B.unfoldTree (right makeBranchNest . g)
  where makeBranchNest (x,ss,(sl,sr)) = ((x, unfoldNest f g ss), sl, sr)

root :: Nest a b -> Either b a
root = elimNest B.root (B.elimTree (\(x,_) _ _ -> Right x) Left)

children :: Nest a b -> Maybe (Nest a b, Nest a b)
children = elimNest (fmap (bimap Flat Flat) . B.children) (fmap (bimap Nest Nest) . B.children)

nest :: Nest a b -> Maybe (Nest a b)
nest = elimNest (const Nothing) (either (const Nothing) (Just . snd) . B.root)

mapNTree :: (a -> c) -> (b -> d) -> NTree a b -> NTree c d
mapNTree f g = B.mapTree (bimap f (mapNest f g)) g

mapNest :: (a -> c) -> (b -> d) -> Nest a b -> Nest c d
mapNest f g = elimNest (Flat . B.mapTree f g) (Nest . mapNTree f g)

flood :: (a -> b -> (d,a,(a,a))) -> (a -> b -> (d,a,a)) -> (a -> c -> e) -> a -> Nest b c -> Nest d e
flood f g h c = elimNest (Flat . B.flood g h c) (Nest . B.flood floodNestBranch h c)
  where floodNestBranch c' (x,nst) = ((x',flood f g h subc nst),lc,rc)
          where (x',subc,(lc,rc)) = f c' x

drain :: (a -> c -> (c,c) -> c) -> (a -> c -> c -> c) -> (b -> c) -> Nest a b -> c
drain f g h = elimNest (B.drain g h) (B.drain drainNestBranch h)
  where drainNestBranch (x,nst) suml sumr = f x (drain f g h nst) (suml,sumr)
