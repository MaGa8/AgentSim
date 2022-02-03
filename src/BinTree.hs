{-# LANGUAGE ScopedTypeVariables, TupleSections, BangPatterns #-}

module BinTree
  (
    BinTree(..), elimTree, unfoldTree, joinTree, mapTree
  , unfoldTree'
  , root, children, leaves
  , isLeaf
  , BinTreeU(..), withBinTreeU
  , drain, flood, floodM, echo, echoM, visit
  ) where

import Data.Bifunctor
import Data.Tuple
import qualified Data.List.NonEmpty as N
import Control.Monad.State

data BinTree a b = Branch a (BinTree a b) (BinTree a b) | Leaf b deriving Show

unfoldTree :: (a -> Either c (b, a, a)) -> a -> BinTree b c
unfoldTree f = either Leaf (\(x, ol, or) -> Branch x (unfoldTree f ol) (unfoldTree f or)) . f
  
unfoldTree' :: (a -> Either c (b, a, a)) -> a -> BinTree b c
unfoldTree' f = either Leaf (\(x, ol, or) -> let
                                left = unfoldTree f ol
                                right = unfoldTree f or
                                in left `seq` right `seq` x `seq` Branch x (unfoldTree f ol) (unfoldTree f or)) . f

-- | builds tree bottom up from leaf values that are combined into a binary tree as complete/as low as possible
joinTree :: (Foldable t) => (a -> a -> a) -> t a -> BinTree a a
joinTree f = completeFull f . balanceLeaves f

completeFull :: (a -> a -> a) -> [BinTree a a] -> BinTree a a
completeFull f [t] = t
completeFull f ts = completeFull f . map (pair2tree f) $ mkpairs [] ts

balanceLeaves :: (Foldable t) => (a -> a -> a) -> t a -> [BinTree a a]
balanceLeaves f = uncurry arrangeExtra . bimap (map Leaf) (map Leaf) . powerlist 2
  where
    -- arrangePairs = map (pair2tree f) . powers2pairs
    -- arrangeExtra extra = zipWith (\x (y, z) -> triple2tree f (x, y, z)) extra . powers2pairs
    arrangeExtra (x : tra) (y : rem) = pair2tree f (x,y) : arrangeExtra tra rem
    arrangeExtra [] rem = rem

pair2tree :: (a -> a -> a) -> (BinTree a a, BinTree a a) -> BinTree a a
pair2tree f (left, right) = Branch (rootU left `f` rootU right) left right

triple2tree :: (a -> a -> a) -> (BinTree a a, BinTree a a, BinTree a a) -> BinTree a a
triple2tree f (leftleft, leftright, right) = pair2tree f (pair2tree f (leftleft, leftright), right)

powers2pairs :: [[a]] -> [(a,a)]
powers2pairs = concatMap (mkpairs [])

mkpairs :: [(a,a)] -> [a] -> [(a,a)]
mkpairs pairs (x1 : x2 : xs) = mkpairs ((x1, x2) : pairs) xs
mkpairs pairs _ = pairs

-- Arranges elements into remainder and a list with a cardinality that is a power of base
powerlist :: (Foldable t) => Int -> t a -> ([a], [a])
powerlist base = bimap snd (($ []) . snd) . foldr (\x -> move . first (add x)) ((0, []), (base, id))
  where
    add x (nbuf, buf) = (nbuf + 1, x : buf)
    move a@((nbuf, buf), (nextpow, fpowers))
      | nbuf == nextpow = ((nextpow, []), (base*nextpow, fpowers . (++ buf))) -- performance sink, use Dlist?
      | otherwise = a
    analyze ((_, []), (_, powers)) = Right powers
    analyze ((_, buf), (_, powers)) = Left (buf, powers)
    

elimTree :: (a -> BinTree a b -> BinTree a b -> c) -> (b -> c) -> BinTree a b -> c
elimTree fb _ (Branch x lt rt) = fb x lt rt
elimTree _ fl (Leaf y) = fl y

mapTree :: (a -> c) -> (b -> d) -> BinTree a b -> BinTree c d
mapTree fb fl = elimTree (\x lt rt -> Branch (fb x) (mapTree fb fl lt) (mapTree fb fl rt)) (Leaf . fl)

-- | Yields the root of the tree wrapped in either Left (stop, reached the bottom) or Right (keep going)
root :: BinTree a b -> Either b a
root = elimTree (\x _ _ -> Right x) Left

rootU :: BinTree a a -> a
rootU = either id id . root

children :: BinTree a b -> Maybe (BinTree a b, BinTree a b)
children = elimTree (\_ l -> Just . (,) l) (const Nothing)

leaves :: BinTree a b -> N.NonEmpty b
leaves = N.fromList . drain (const (++)) return

paths :: BinTree a b -> N.NonEmpty ([a],b)
paths = drain addBranch ((N.:| []) . ([],))
  where
    addBranch x pls prs = N.fromList . map (first (x :)) $ N.toList pls ++ N.toList prs

isLeaf :: BinTree a b -> Bool
isLeaf = either (const True) (const False) . root

-- | type with Functor and preorder traversal Foldable instance
newtype BinTreeU a = BinTreeU{ unBinTreeU :: BinTree a a }

withBinTreeU :: (BinTreeU a -> BinTreeU b) -> BinTree a a -> BinTree b b
withBinTreeU f = unBinTreeU . f . BinTreeU

instance Functor BinTreeU where
  fmap f = BinTreeU . mapTree f f . unBinTreeU

instance Foldable BinTreeU where
  foldr f acc t = case unBinTreeU t of
    Leaf x -> f x acc
    Branch x left right -> let
      (leftU, rightU) = (BinTreeU left, BinTreeU right)
      ffoldr = flip (foldr f)
      in f x . ffoldr leftU $ ffoldr rightU acc

drain :: (a -> c -> c -> c) -> (b -> c) -> BinTree a b -> c
drain fb fl = elimTree (\x lt rt -> fb x (drain fb fl lt) (drain fb fl rt)) fl

drainM :: Monad m => (a -> c -> c -> m c) -> (b -> m c) -> BinTree a b -> m c
drainM fb = drain (\x ml mr -> (\r -> (\l -> fb x l r) =<< ml) =<< mr)

echo :: (a -> e -> e -> (c,e)) -- ^ echo at branch
     -> (b -> (d,e)) -- ^ echo at leaf
     -> BinTree a b -> (BinTree c d, e)
echo fb fl = drain drainBranch drainLeaf
  where
    drainLeaf = first Leaf . fl
    drainBranch x (tl,el) (tr,er) = first (\x' -> Branch x' tl tr) $ fb x el er

echoM :: Monad m =>
         (a -> e -> e -> m (c,e))
      -> (b -> m (d,e))
      -> BinTree a b -> m (BinTree c d,e)
echoM fb fl = drain echoBranch echoLeaf
  where
    echoLeaf = fmap (first Leaf) . fl
    echoBranch x l r = do
      (tl,el) <- l
      (tr,er) <- r
      first (\x' -> Branch x' tl tr) <$> fb x el er

flood :: (a -> b -> (d, a, a)) -> (a -> c -> e) -> a -> BinTree b c -> BinTree d e
flood fb fl o = elimTree floodBranch (Leaf . fl o)
  where floodBranch x lt rt = let
          (x', ol, or) = fb o x
          in Branch x' (flood fb fl ol lt) (flood fb fl or rt)

floodM :: Monad m =>
           (a -> b -> m (d,a,a)) -- ^ process wave for branch case producing a new value at two split waves
        -> (a -> m a) -- ^ continuation for the left subtree
        -> (a -> m a) -- ^ continuation for the right subtree
        -> (a -> c -> m e) -- ^ process wave at leaf node producing only a new value
        -> a -> BinTree b c -> m (BinTree d e)
floodM fb cl cr fl w = elimTree floodBranch floodLeaf
  where
    floodBranch x l r = do
      (x',wl,wr) <- fb w x
      l' <- cl wl >>= (\wl' -> floodM fb cl cr fl wl' l)
      r' <- cr wr >>= (\wr' -> floodM fb cl cr fl wr' r)
      return $ Branch x' l' r'
    floodLeaf = fmap Leaf . fl w

-- | Flood the tree and immediately drain the flooded values.
-- Equivalent to flood followed by drain but does not construct the intermediate tree and provides choice about subtrees to visit.
visit :: (a -> b -> (d, Maybe a, Maybe a)) -- ^ pass on the wave to subtrees of choice producing a flood value of type d
      -> (d -> Maybe e -> Maybe e -> e) -- ^ collect the flood value and the echoes from the subtrees producing a new echo
      -> (a -> c -> e) -- ^ produce an echo directly from the wave at leaves
      -> a -> BinTree b c -> e
visit !fDownBranch !fUpBranch !fLeaf iniacc = elimTree (visitBranch fDownBranch fUpBranch fLeaf iniacc) (fLeaf iniacc)

visitBranch :: (a -> b -> (d, Maybe a, Maybe a)) -> (d -> Maybe e -> Maybe e -> e) -> (a -> c -> e) -> a -> b -> BinTree b c -> BinTree b c -> e
visitBranch !fDownBranch !fUpBranch !fLeaf wave x !left !right = fUpBranch inter (echo left <$> leftWave) (echo right <$> rightWave)
  where
    (inter, !leftWave, !rightWave) = fDownBranch wave x
    echo sub wave' = visit fDownBranch fUpBranch fLeaf wave' sub

-- | turn inner nodes into leaves
trim :: (a -> Either b a -> Either b a -> Maybe b) -> BinTree a b -> BinTree a b
trim f = elimTree try Leaf
  where
    try x left right = let
      (leftx, rightx) = (root left, root right)
      in maybe (Branch x (trim f left) (trim f right)) Leaf $ f x leftx rightx
