
module Messiah
  (

  ) where

import Data.Map(Map, (!))
import Data.List(maximumBy)
import qualified Data.Map as M
import Data.Bifunctor

import Control.Monad.State

import System.Random as R

import Sim

type R2 = (Double, Double)

newtype Move = Move{ velocity :: R2 }
data Messiah = Messiah{ boundary :: (R2, R2), nextStop :: R2, oracle :: StdGen }
newtype Follower = Follower{ holyPlace :: R2 }
newtype Message = ISawHim R2

data AgentData = AgentData{ getSpec :: Either Messiah Follower, getMove :: Move }

messiah :: Double -> Move -> Messiah -> Agent R2 Message AgentData
messiah radius move m = Agent{ talk = speak, act = behave, see = ballSight radius, core = AgentData{ getSpec = Left m, getMove = move} }

follower :: Double -> Move -> Follower -> Agent R2 Message AgentData
follower radius move follower = Agent{ talk = speak, act = behave, see = ballSight radius, core = AgentData{ getSpec = Right follower, getMove = move} }

-- | generates stream of positions where generator at stream element is the generator after the operation
generatePositions :: (RandomGen g) => (R2, R2) -> g -> [(R2, g)]
generatePositions bound@((x1,y1), (x2,y2)) g = let ((x,g'), (y,g'')) = (randomR (x1,x2) g, randomR (y1,y2) g') in ((x,y),g'') : generatePositions bound g''

operate :: (Move -> Either Messiah Follower -> Either Messiah Follower) -> AgentData -> AgentData
operate f agdat = agdat{ getSpec = f (getMove agdat) (getSpec agdat) }

type Instance = Agent R2 Message AgentData

mkBox :: Double -> R2 -> (R2, R2)
mkBox r (x,y) = ((x - r, y - r), (x + r, y + r))

ballSight :: Double -> Sight R2 a
ballSight radius pos _ = mkBox radius pos

messiahSpeech :: R2 -> Move -> Messiah -> Map AgentData R2 -> Map AgentData Message
messiahSpeech pos _ _ = M.map (const $ ISawHim pos)

followerSpeech :: R2 -> Move -> Follower -> Map AgentData R2 -> Map AgentData Message
followerSpeech _ _ follower = M.map (const . ISawHim $ holyPlace follower)

speak :: Speech R2 Message AgentData
speak pos ag = either (messiahSpeech pos (getMove ag)) (followerSpeech pos (getMove ag)) $ getSpec ag

messiahAct :: Move -> Behavior R2 Message Messiah
messiahAct mv pos messiah _
  | pos == nextStop messiah = let (x, gen') = randomR (bimap fst fst $ boundary messiah) $ oracle messiah
                                  (y, gen'') = randomR (bimap snd snd $ boundary messiah) gen'
                              in (messiah{ nextStop = (x,y), oracle = gen'' }, pos)
  | otherwise = (messiah, moveTowards (nextStop messiah) (velocity mv) pos)

minMag :: (Ord a, Num a) => a -> a -> a
minMag x y = if abs x < abs y then x else y

moveTowards :: R2 -> R2 -> R2 -> R2
moveTowards (finalx,finaly) (vx,vy) (x,y) = (x + minMag vx (finalx - x), y + minMag vy (finaly - y))

followerAct :: Move -> Behavior R2 Message Follower
followerAct mv pos fol messages = let dest = majorityVote $ map (\(ISawHim loc) -> loc) messages
                                  in (fol{ holyPlace = dest }, moveTowards dest (velocity mv) pos)

majorityVote :: (Ord a) => [a] -> a
majorityVote vote = let freqs = frequency vote in maximumBy (\x y -> compare (freqs ! x) (freqs ! y)) (M.keys freqs)

frequency :: (Foldable t, Ord a) => t a -> Map a Int
frequency = foldl (\table x -> M.insertWith (+) x 1 table) mempty

behave :: Behavior R2 Message AgentData
behave pos agdat = first (joinAgent agdat) . forkAgent (\mv messiah -> first Left . messiahAct mv pos messiah) (\mv follower -> first Right . followerAct mv pos follower) agdat

forkAgent :: (Move -> Messiah -> a) -> (Move -> Follower -> a) -> AgentData -> a
forkAgent f g agdat = either (f (getMove agdat)) (g (getMove agdat)) $ getSpec agdat

joinAgent :: AgentData -> Either Messiah Follower -> AgentData
joinAgent agdat = either (\messiah -> agdat{ getSpec = Left messiah }) (\follower -> agdat{ getSpec = Right follower })
