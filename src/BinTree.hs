{-# LANGUAGE TupleSections #-}
module BinTree
  (
    BinTree(..), elimTree, unfoldTree, mapTree
  , root, children, leaves
  , isLeaf
  , drain, flood, floodM, echo, echoM
  ) where

import Data.Bifunctor
import Data.Tuple
import qualified Data.List.NonEmpty as N

data BinTree a b = Branch a (BinTree a b) (BinTree a b) | Leaf b deriving Show

unfoldTree :: (a -> Either c (b, a, a)) -> a -> BinTree b c
unfoldTree f = either Leaf (\(x, ol, or) -> Branch x (unfoldTree f ol) (unfoldTree f or)) . f

elimTree :: (a -> BinTree a b -> BinTree a b -> c) -> (b -> c) -> BinTree a b -> c
elimTree fb _ (Branch x lt rt) = fb x lt rt
elimTree _ fl (Leaf y) = fl y

mapTree :: (a -> c) -> (b -> d) -> BinTree a b -> BinTree c d
mapTree fb fl = elimTree (\x lt rt -> Branch (fb x) (mapTree fb fl lt) (mapTree fb fl rt)) (Leaf . fl)

-- | Yields the root of the tree wrapped in either Left (stop, reached the bottom) or Right (keep going)
root :: BinTree a b -> Either b a
root = elimTree (\x _ _ -> Right x) Left

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
  where floodBranch x lt rt = Branch x' (flood fb fl ol lt) (flood fb fl or rt)
          where (x', ol, or) = fb o x

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
