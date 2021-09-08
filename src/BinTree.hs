
module BinTree
  (
    BinTree(..), elimTree, unfoldTree, mapTree
  , root, children
  , isLeaf
  , drain, flood
  ) where

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

isLeaf :: BinTree a b -> Bool
isLeaf = either (const True) (const False) . root

drain :: (a -> c -> c -> c) -> (b -> c) -> BinTree a b -> c
drain fb fl = elimTree (\x lt rt -> fb x (drain fb fl lt) (drain fb fl rt)) fl

flood :: (a -> b -> (d, a, a)) -> (a -> c -> e) -> a -> BinTree b c -> BinTree d e
flood fb fl o = elimTree floodBranch (Leaf . fl o)
  where floodBranch x lt rt = Branch x' (flood fb fl ol lt) (flood fb fl or rt)
          where (x', ol, or) = fb o x
