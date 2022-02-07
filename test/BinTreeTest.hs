{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module BinTreeTest
  (
    testBinTree
  , prop_constructFromList, prop_drain, prop_echo, prop_flood
  ) where

import Test.QuickCheck
import Test.QuickCheck.All

import qualified Data.List.NonEmpty as N
import qualified Data.List as L
import Data.Maybe
import Data.Ratio
import qualified Data.Map as M
import Data.Bifunctor

import Control.Arrow((&&&))

import BinTree


-- test construction: produce tree by splitting list in half recursively
-- check that leaves contain list elements
prop_constructFromList :: [Int] -> Bool
prop_constructFromList [] = True
prop_constructFromList xs = all (maybe True (`elem` xs)) . leaves $ constructFromList xs

constructFromList :: [Int] -> BinTree () (Maybe Int)
constructFromList = unfoldTree halve
  where
    halve [] = Left Nothing
    halve [x] = Left $ Just x
    halve xs = let no2 = floor $ fromIntegral (length xs) / 2
                   (ls,rs) = splitAt no2 xs
               in Right ((),ls,rs)

mkBinSearchTree :: [Int] -> BinTree Int (Maybe Int)
mkBinSearchTree = unfoldTree divide
  where
    divide [] = Left Nothing
    divide [x] = Left $ Just x
    divide (x : xs) = let
      (lefts, rights) = L.partition (< x) xs
      in Right (x, lefts, rights)

-- construct tree from list and check that echo is equal to sum over leaves
prop_drain :: [Int] -> Bool
prop_drain [] = True
prop_drain xs = sum xs == drain (const (+)) (fromMaybe 0) (constructFromList xs)

-- check that height is equal to log listlen up to rounding
prop_echo :: [Int] -> Bool
prop_echo [] = True
prop_echo xs = let t = mkHeightTree xs
                   h = either id id $ root t
                   n = length xs
                   l = log . fromIntegral $ length xs
                   lmax = 2^h
                   lmin = if h > 0 then 2^(h-1) + 1 else 1
              in lmin <= n && n <= lmax

mkHeightTree :: [Int] -> BinTree Int Int
mkHeightTree = fst . echo heightBranch heightLeaf . constructFromList
  where
    heightBranch _ l r = let h = 1 + max l r in (h,h)
    heightLeaf = const (0,0)

-- precondition: argument is a positive integer
constructHeightTree :: Int -> BinTree () ()
constructHeightTree n
  | n <= 0 = Leaf ()
  | otherwise = let sub = constructHeightTree (n-1) in Branch () sub sub

-- binomial coefficient
binoc :: Int -> Int -> Int
binoc _ 0 = 1
binoc 0 _ = 1
binoc n k
  | n == k = 1
  | otherwise = binoc (n-1) (k-1) + binoc (n-1) k

counts :: (Ord a) => [a] -> M.Map a Int
counts = M.map length . M.fromListWith (++) . map (\x -> (x,[x]))

-- | Build BST for list and collect all numbers with fold
prop_fold :: [Int] -> Bool
prop_fold ns = all (`elem` ns) ns' && all (`elem` ns') ns
  where
    ns' = catMaybes . foldr (:) [] . BinTreeU . mapTree Just id $ mkBinSearchTree ns

-- from node value v send (v,v+0) to the children
-- if we split n times then the leaves are the values from 0 .. 2^n
prop_flood :: Positive Int -> Bool
prop_flood nnodes = let
  n = max 1 . ceiling . log . fromIntegral $ getPositive nnodes
  combinationTree = flood (\x _ -> (x,x,x+1)) const 0 $ constructHeightTree n
  valueCounts = counts . N.toList $ leaves combinationTree
  in and $ M.mapWithKey (\k c -> binoc n k == c) valueCounts

-- Build a BST.  Trim all nodes below primes.  Verify only the numbers below prime numbers are missing.
prop_trim :: [Int] -> Bool
prop_trim xs = isEqualSet (catMaybes numbersUntrimmed) numbersTrimmed
  where
    numbersUntrimmed = drain (\x lefts rights -> Just x : if isPrime x then [] else lefts ++ rights) return bst
    numbersTrimmed = drain (\x lefts rights -> x : lefts ++ rights) (maybe [] return) trimmed
    trimmed = trim (\x _ _ -> if isPrime x then Just (Just x) else Nothing) bst
    bst = mkBinSearchTree xs

isEqualSet :: (Eq a, Foldable t) => t a -> t a -> Bool
isEqualSet xs ys = all (`elem` ys) xs && all (`elem` xs) ys

isPrime :: Int -> Bool
isPrime n = not $ any ((== 0) . rem n) [2 .. upper]
  where
    upper = floor . sqrt $ fromIntegral n

-- Build tree by halving one list. Split the other, longer list according to that tree and collect the elements again. Check the original list is recovered at every node.
prop_visit :: [Int] -> [Int] -> Bool
prop_visit [] [] = True
prop_visit xs ys
  | length xs < length ys = runVisit xs ys
  | otherwise = runVisit ys xs
  where
    runVisit xs' ys' = fst . visit divideFlood collectEcho (\zs -> const (True, zs)) ys' $ constructFromList xs'

divideFlood :: [a] -> b -> ([a], Maybe [a], Maybe [a])
divideFlood xs _ = (xs, leftHalf, rightHalf)
  where
    l = length xs
    halfSize = floor $ l % 2
    mdivisible = if l > 1 then Just xs else Nothing
    (leftHalf, rightHalf) = (take halfSize <$> mdivisible, drop halfSize <$> mdivisible)

collectEcho :: Eq a => [a] -> Maybe (Bool, [a]) -> Maybe (Bool, [a]) -> (Bool, [a])
collectEcho xs mlefts mrights = (subsOkay && subsAddUp, xs)
  where
    subsOkay = maybe True fst mlefts && maybe True fst mrights
    subsAddUp = let
      mSubsAdded = (++) <$> (snd <$> mlefts) <*> (snd <$> mrights)
      in maybe True (xs ==) mSubsAdded

-- testBinTree :: IO Bool
return []
testBinTree = $quickCheckAll 

