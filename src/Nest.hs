{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Nest
  (
    Nest(..), BinTree(..), module B
  , NestNode, elimNestNode, mkNestNode
  , elimNest, mkNest, nestTree, unfoldNest, unfoldNest'
  , isFlat, isLeaf, toNest, toFlat
  , root, roots, children, nest
  , mapNest, flood, floodFull, drain, echo, zipNest
  , prettyPrintNest
  ) where

import Data.Maybe
import Data.Bifunctor

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import qualified BinTree as B
import BinTree(BinTree(..))

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

nestTree :: (a -> (b, Nest b c)) -> BinTree a a -> NTree b c
nestTree f = B.mapTree f f

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

drain :: (a -> Maybe c -> Maybe (c,c) -> c) -> (b -> c) -> Nest a b -> c
drain fb fl = elimNest (B.drain fbFlat fl) (B.drain fbNest flNest . B.mapTree reduceNest reduceNest)
  where
    fbFlat x left right = fb x Nothing (Just (left, right))
    fbNest (x,nst) left right = fb x (Just nst) (Just (left, right))
    flNest (x,nst) = fb x (Just nst) Nothing
    reduceNest = elimNestNode (\x nst -> (x, drain fb fl nst))

adaptorDrainByCases :: (a -> c -> (c,c) -> c) -> (a -> c -> c) -> (a -> c -> c -> c) -> a -> Maybe c -> Maybe (c,c) -> c
adaptorDrainByCases fInnerNest _ _ x (Just nest) (Just sub) = fInnerNest x nest sub
adaptorDrainByCases _ fLeafNest _ x (Just nest) Nothing = fLeafNest x nest
adaptorDrainByCases _ _ fInnerFlat x _ (Just (left, right)) = fInnerFlat x left right

adaptFlatBranch :: (a -> Maybe b -> Maybe (b,b) -> c) -> a -> b -> b -> c
adaptFlatBranch f x l r = f x Nothing (Just (l,r))

echo :: forall a b c d e. (a -> Maybe e -> Maybe (e,e) -> (c,e))
        -> (b -> (d,e))
        -> Nest a b -> (Nest c d, e)
echo fb fl = elimNest (first Flat . B.echo (adaptFlatBranch fb) fl) (first Nest . B.echo handleNestBranch handleNestLeaf)
  where
    handleNestBranch :: (a, Nest a b) -> e -> e -> ((c, Nest c d), e)
    handleNestBranch (x,nst) le re = let (nst', nste) = echo fb fl nst in first (,nst') $ fb x (Just nste) (Just (le,re))
    handleNestLeaf :: (a, Nest a b) -> ((c, Nest c d), e)
    handleNestLeaf (x,nst) = let (nst', nste) = echo fb fl nst in first (,nst') $ fb x (Just nste) Nothing

-- echoFull :: (a -> e -> (e,e) -> (c,e)) -- ^ echo for nested inner node
--          -> (a -> e -> (c,e)) -- ^ echo for nested leaf
--          -> (a -> e -> e -> (c,e)) -- ^ echo for flat inner node
--          -> (b -> (d,e)) -- ^ echo for flat leaf
--          -> Nest a b -> (Nest c d,e)
-- echoFull fnb fnl ffb ffl = either id id . drainFull echoNestBranch echoNestLeaf echoFlatBranch echoFlatLeaf
--   where
--     echoNestBranch x nst ((l,el),(r,er)) = let (n,e) = either id id nst
--                                            in first (\x' -> Nest $ Branch (x',n) (toNest l) (toNest r)) $ fnb x e (el,er)
--     echoNestLeaf x nst = let (n,e) = either id id nst in first (\x' -> Nest $ Leaf (x',n)) $ fnl x e
--     echoFlatBranch x (l,el) (r,er) = first (\x' -> Flat $ Branch x' (toFlat l) (toFlat r)) $ ffb x el er
--     echoFlatLeaf y = first (Flat . Leaf) $ ffl y

-- -- first combine echo from subtrees then combine echo from nested tree
-- echo :: (a -> e -> (c,e)) -- ^ combine value and echo from nested tree
--      -> (a -> e -> e -> (c,e)) -- ^ combine value and echoes from subtrees
--      -> (c -> e -> c -> e -> (c,e)) -- ^ integrate product from nested tree and from subtree subtrees
--      -> (b -> (d,e))
--      -> Nest a b -> (Nest c d, e)
-- echo fnest fsub fint = echoFull echoNestBranch fnest fsub
--   where
--     echoNestBranch x en (el,er) = let (nx,ne) = fnest x en
--                                       (sx,se) = fsub x el er
--                                   in fint nx ne sx se

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
prettyPrintNest maxd = ($ "") . drain (adaptorDrainByCases printNestBranch printNestLeaf printFlatBranch) printFlatLeaf . labelNestLevels
  where
    printValuePadded x pad = putStrLn $ pad ++ show x
    -- accumulated value is String -> IO () where String argument is the padding to be applied to every line
    printNestBranch :: (a,Int) -> PadShow -> (PadShow,PadShow) -> String -> IO ()
    printNestBranch (x,n) nstio (lio,rio) pad = do
      printValuePadded x pad
      when (maybe True (n <) maxd) $ nstio (pad ++ "^^") >> putStrLn ""
      lio $ pad ++ "Nl "
      rio $ pad ++ "Nr "
    printNestLeaf :: (a,Int) -> PadShow -> String -> IO ()
    printNestLeaf (x,n) nstio pad = do
      printValuePadded x pad
      when (maybe True (n <) maxd) $ nstio (pad ++ "^^") >> putStrLn ""
    printFlatBranch :: (a,Int) -> PadShow -> PadShow -> String -> IO ()
    printFlatBranch (x,_) lio rio pad = do
      printValuePadded x pad
      lio (pad ++ "Fl ")
      rio (pad ++ "Fr ")
    printFlatLeaf :: (b,Int) -> String -> IO ()
    printFlatLeaf (x,_) = printValuePadded x

prettyPrintNest' :: forall a b. (Show a,Show b) => Maybe Int -> Nest a b -> IO ()
prettyPrintNest' maxd = ($ "") . drain printBranch printLeaf . labelNestLevels
  where
    printBranch = undefined -- treat cases jointly
    printLeaf = undefined