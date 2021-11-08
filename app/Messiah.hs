
module Messiah
  (
    Instance, Message, Uid, AgentData(..), Messiah(..), Follower(..), Move(..)
  , messiah, follower
  , appear
  , R2, comparatorSeq
  , generatePositions
  , debugMessages, debugAgent
  ) where

import Data.Map(Map, (!))
import Data.List(maximumBy)
import Data.List.NonEmpty(NonEmpty(..))
import qualified Data.Map as M
import Data.Bifunctor
import Data.Maybe

import Control.Monad.State

import System.Random as R

import Debug.Trace

import Lib
import Vis

type R2 = (Double, Double)

comparatorSeq :: NonEmpty (R2 -> R2 -> Ordering)
comparatorSeq = (\x y -> fst x `compare` fst y) :| [\x y -> snd x `compare` snd y]

newtype Move = Move{ velocity :: R2 }
data Messiah = Messiah{ boundary :: (R2, R2), nextStop :: R2, oracle :: StdGen }
newtype Follower = Follower{ holyPlace :: Maybe R2 }
newtype Message = ISawHim R2

type Uid = Int
data AgentData = AgentData{ getId :: Uid, getSpec :: Either Messiah Follower, getMove :: Move }
type Instance = Agent R2 Message AgentData


instance Eq AgentData where
  a1 == a2 = getId a1 == getId a2

instance Ord AgentData where
  a1 <= a2 = getId a1 <= getId a2

messiah :: Uid -> Double -> Move -> Messiah -> Instance
messiah ident radius move m = Agent{ talk = speak, act = behave, see = ballSight radius, core = AgentData{ getId = ident, getSpec = Left m, getMove = move} }

follower :: Uid -> Double -> Move -> Follower -> Instance
follower ident radius move follower = Agent{ talk = speak, act = behave, see = ballSight radius, core = AgentData{ getId = ident, getSpec = Right follower, getMove = move} }

elimAgentData :: (Uid -> Move -> Either Messiah Follower -> a) -> AgentData -> a
elimAgentData f agdat = f (getId agdat) (getMove agdat) (getSpec agdat)

elimWithMessiah :: (Uid -> Move -> Messiah -> a) -> AgentData -> Maybe a
elimWithMessiah f = elimAgentData (\uid move -> either (Just . f uid move) (const Nothing))

elimWithFollower :: (Uid -> Move -> Follower -> a) -> AgentData -> Maybe a
elimWithFollower f = elimAgentData (\uid move -> either (const Nothing) (Just . f uid move))

isMessiah, isFollower :: AgentData -> Bool
isMessiah = fromMaybe False . elimWithMessiah (\_ _ _ -> True)
isFollower = fromMaybe False . elimWithFollower (\_ _ _ -> True)

-- | generates stream of positions where generator at stream element is the generator after the operation
generatePositions :: (RandomGen g) => (R2, R2) -> g -> [(R2, g)]
generatePositions bound@((x1,y1), (x2,y2)) g = let ((x,g'), (y,g'')) = (randomR (x1,x2) g, randomR (y1,y2) g') in ((x,y),g'') : generatePositions bound g''

appear :: Instance -> R2 -> Appearance
appear agent pos
  | isMessiah (core agent) = Appearance ( centerRectAround pos 1 1
                                           , (255, 0, 0))
  | isFollower (core agent) = Appearance ( centerRectAround pos 1 1
                                            , (0, 255, 0))

centerRectAround :: R2 -> Int -> Int -> Shape Int
centerRectAround (x,y) w h = Rectangle (xfloor - halfw, yfloor - halfh) w h
  where
    (xfloor, yfloor) = (floor x, floor y)
    (halfw, halfh) = (floor $ fromIntegral w / 2, floor $ fromIntegral h / 2)

operate :: (Move -> Either Messiah Follower -> Either Messiah Follower) -> AgentData -> AgentData
operate f agdat = agdat{ getSpec = f (getMove agdat) (getSpec agdat) }

mkBox :: Double -> R2 -> (R2, R2)
mkBox r (x,y) = ((x - r, y - r), (x + r, y + r))

ballSight :: Double -> Sight R2 a
ballSight radius pos _ = mkBox radius pos

messiahSpeech :: R2 -> Move -> Messiah -> Map AgentData R2 -> Map AgentData Message
messiahSpeech pos _ _ = M.map (const $ ISawHim pos)

followerSpeech :: R2 -> Move -> Follower -> Map AgentData R2 -> Map AgentData Message
followerSpeech _ _ follower = maybe mempty (\holyloc -> M.map (const $ ISawHim holyloc)) $ holyPlace follower

speak :: Speech R2 Message AgentData
speak pos ag = either (messiahSpeech pos (getMove ag)) (followerSpeech pos (getMove ag)) $ getSpec ag

pipeTrace :: (a -> String) -> a -> a
pipeTrace f x = trace (f x) x

debugMessiahChange, debugMessiahContinue :: R2 -> Messiah -> R2 -> String
debugMessiahChange oldpos mess newpos = "messiah changes goal " ++ show (nextStop mess) ++ " and moves from " ++ show (bimap floor floor oldpos) ++ " to " ++ show (bimap floor floor newpos) ++ " gen " ++ show (oracle mess)
debugMessiahContinue oldpos mess newpos = "messiah moves from " ++ show (bimap floor floor oldpos) ++ " to " ++ show (bimap floor floor newpos) ++ " towards " ++ show (bimap floor floor $ nextStop mess)

-- | Messiah is exclusively in one of the following states:
-- (1) no goal: messiah generates goal and transistions to state (2)
-- (2) has distant goal: messiah moves towards goal. 
-- (3) reached goal: messiah voids goal
messiahAct :: Move -> Behavior R2 Message Messiah
messiahAct mv pos messiah _
  | pos == nextStop messiah = let (x, gen') = randomR (bimap fst fst $ boundary messiah) $ oracle messiah
                                  (y, gen'') = randomR (bimap snd snd $ boundary messiah) gen'
                                  -- in pipeTrace (uncurry (debugMessiahChange pos)) (messiah{ nextStop = (x,y), oracle = gen'' }, moveTowards (x,y) (velocity mv) pos)
                              in (messiah{ nextStop = (x,y), oracle = gen'' }, moveTowards (x,y) (velocity mv) pos)
  -- x | otherwise = pipeTrace (uncurry (debugMessiahContinue pos)) (messiah, moveTowards (nextStop messiah) (velocity mv) pos)
  | otherwise = (messiah, moveTowards (nextStop messiah) (velocity mv) pos)

minMag :: (Ord a, Num a) => a -> a -> a
minMag x y = if abs x < abs y then x else y

moveTowards :: R2 -> R2 -> R2 -> R2
moveTowards (finalx,finaly) (vx,vy) (x,y) = (x + minMag (signum gapx * signum vx * vx) gapx, y + minMag (signum gapy * signum vy * vy) gapy)
  where
    (gapx, gapy) = (finalx - x, finaly - y)

debugFollowerIdle :: [Message] -> (Follower, R2) -> String
debugFollowerIdle msgs (fol, newpos) = "follower idle at " ++ show newpos ++ " believes " ++ show (holyPlace fol) ++ " received " ++ show (map (\(ISawHim loc) -> bimap floor floor loc) msgs)

debugFollowerBusy :: R2 -> (Follower, R2) -> String
debugFollowerBusy oldpos (fol, newpos) = "follower busy moving " ++ show oldpos ++ " to " ++ show newpos ++ " goal " ++ show (holyPlace fol)

-- | Follower is a state machine
-- (1) follower does'nt believe in a holy place:  It will listen to messages to determine the holy place. 
-- (2) follower believes in a distant holy place: It moves towards the holy place
-- (3) follower reached holy place: It stops believing in the holy place
followerAct :: Move -> Behavior R2 Message Follower
followerAct mv pos fol messages = maybe findHolyPlace moveHolyPlace $ holyPlace fol
  where
    -- findHolyPlace = pipeTrace (debugFollowerIdle messages) (fol{ holyPlace = majorityVote $ map (\(ISawHim loc) -> loc) messages}, pos)
    findHolyPlace = (fol{ holyPlace = majorityVote $ map (\(ISawHim loc) -> loc) messages}, pos)
    moveHolyPlace holyloc
      | isClose 0.0001 pos holyloc = (fol{ holyPlace = Nothing }, holyloc)
      -- x | otherwise = pipeTrace (debugFollowerBusy pos) (fol, moveTowards holyloc (velocity mv) pos)
      | otherwise = (fol, moveTowards holyloc (velocity mv) pos)

isClose :: Double -> R2 -> R2 -> Bool
isClose eps (x1,y1) (x2,y2) = (x1 - x2)^2 + (y1 - y2)^2 <= eps

majorityVote :: (Ord a) => [a] -> Maybe a
majorityVote [] = Nothing
majorityVote vote = let freqs = frequency vote in Just $ maximumBy (\x y -> compare (freqs ! x) (freqs ! y)) (M.keys freqs)

frequency :: (Foldable t, Ord a) => t a -> Map a Int
frequency = foldl (\table x -> M.insertWith (+) x 1 table) mempty

behave :: Behavior R2 Message AgentData
behave pos agdat = first (joinAgent agdat) . forkAgent (\mv messiah -> first Left . messiahAct mv pos messiah) (\mv follower -> first Right . followerAct mv pos follower) agdat

forkAgent :: (Move -> Messiah -> a) -> (Move -> Follower -> a) -> AgentData -> a
forkAgent f g agdat = either (f (getMove agdat)) (g (getMove agdat)) $ getSpec agdat

joinAgent :: AgentData -> Either Messiah Follower -> AgentData
joinAgent agdat = either (\messiah -> agdat{ getSpec = Left messiah }) (\follower -> agdat{ getSpec = Right follower })

debugMessages :: Map Instance [Message] -> String
debugMessages = (++ "\n") . concatMap toString . M.toList
  where
    toString (ag, ins) = show (getId $ core ag) ++ " gets " ++ concatMap showMessage ins ++ "\n"
    showMessage (ISawHim pos) = show $ bimap floor floor pos

debugAgent :: Map Instance R2 -> String
debugAgent = (++ "\n") . concatMap (\(ag, pos) -> (++ "\n") . either (const $ debugMessiah ag pos) (const $ debugFollower ag pos) . getSpec $ core ag) . M.toList

debugMessiah :: Instance -> R2 -> String
debugMessiah ag pos = "messiah " ++ identifier ++ " at " ++ position ++ " status " ++ status
  where
    agdat = core ag
    spec = fromJust $ elimWithMessiah (\_ _ m -> m) agdat
    identifier = show (getId agdat)
    position = show $ bimap floor floor pos
    status = "moving to " ++ show (bimap floor floor $ nextStop spec)

debugFollower :: Instance -> R2 -> String
debugFollower ag pos = "follower " ++ identifier ++ " at " ++ position ++ " status " ++ status
  where
    agdat = core ag
    spec = fromJust $ elimWithFollower (\_ _ f -> f) agdat
    identifier = show (getId agdat)
    position = show $ bimap floor floor pos
    status
      | isJust (holyPlace spec) = "moving to holy " ++ show (bimap floor floor . fromJust $ holyPlace spec)
      | otherwise = "idle"
