
module Messiah
  (
    Instance, Message, Uid, AgentData(..), Messiah(..), Follower(..), Move(..)
  , messiah, follower, initFollower
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

import Control.Applicative((<|>))
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
data Follower = Follower{ holyPlace :: Maybe R2, lastMove :: Maybe R2, num_overshoots :: Int, num_idles :: Int, overshooting :: Maybe Int, idling :: Maybe Int }
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

initFollower :: Int -- ^ number of iterations the agent keeps moving after reaching the target
             -> Int -- ^ number of cylces the agent does nothing after reaching the target and overshooting
             -> Follower
initFollower overshoot_cycles idle_cycles = Follower{ holyPlace = Nothing, lastMove = Nothing, overshooting = Nothing, idling = Nothing, num_overshoots = overshoot_cycles, num_idles = idle_cycles }

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
appear agent pos = elimAgentData (\_ _ -> either messiahAppear followerAppear) $ core agent
  where
    messiahAppear _ = Appearance (centerRectAround pos 1 1, (255, 0, 0))
    followerAppear fol = let color = fromJust $ ((122,122,255) <$ holyPlace fol) <|> ((0,0,255) <$ overshooting fol) <|> ((0,255,255) <$ idling fol) <|> Just (0,255,0)
                         in Appearance (centerRectAround pos 1 1, color)

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
                              in (messiah{ nextStop = (x,y), oracle = gen'' }, fst $ moveTowards (x,y) (velocity mv) pos)
  | otherwise = (messiah, fst $ moveTowards (nextStop messiah) (velocity mv) pos)

minMag :: (Ord a, Num a) => a -> a -> a
minMag x y = if abs x < abs y then x else y

addR2 :: R2 -> R2 -> R2
addR2 (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)

-- | return (new_position, move_vector)
moveTowards :: R2 -> R2 -> R2 -> (R2, R2)
moveTowards (finalx,finaly) (vx,vy) pos@(x,y) = (addR2 pos dmove, dmove)
  where
    (gapx, gapy) = (finalx - x, finaly - y)
    dmove = (minMag (signum gapx * signum vx * vx) gapx, minMag (signum gapy * signum vy * vy) gapy)

debugFollowerIdle :: [Message] -> (Follower, R2) -> String
debugFollowerIdle msgs (fol, newpos) = "follower idle at " ++ show newpos ++ " believes " ++ show (holyPlace fol) ++ " received " ++ show (map (\(ISawHim loc) -> bimap floor floor loc) msgs)

debugFollowerBusy :: R2 -> (Follower, R2) -> String
debugFollowerBusy oldpos (fol, newpos) = "follower busy moving " ++ show oldpos ++ " to " ++ show newpos ++ " goal " ++ show (holyPlace fol)

-- | Follower is a state machine
-- (1) follower is listening for a holy place [initial]. Waits for a message and choose by majority. Transitions: (2)
-- (2) follower got a holy place. Follower moves to holy place, sends tells others to go there too and if it arrived sets overshooting and resets holyPlace. Transitions (3)
-- (3) Follower has overshooting > 0. Follower keeps repeats last motion and decrements overshooting and upon reaching overshooting == 0 sets idling and resets overshooting.  Transitions: (4)
-- (4) follower has idling > 0.  Follower does nothing, decrements idling and upon reaching idling == 0 resets idling.  Transitions: (1)
followerAct :: Move -> Behavior R2 Message Follower
followerAct mv pos fol messages = fromJust $ (moveTo <$> holyPlace fol) <|> (moveOvershoot <$> overshooting fol <*> lastMove fol) <|> (stayIdle <$> idling fol) <|> Just listenForMessage
  where
    moveTo loc
      | isClose 0.0001 pos loc = (fol{holyPlace=Nothing, overshooting=Just (num_overshoots fol)}, pos)
      | otherwise = let (new_pos, v) = moveTowards loc (velocity mv) pos in (fol{lastMove = Just v}, new_pos)
    moveOvershoot 0 _ = (fol{overshooting=Nothing, lastMove=Nothing, idling=Just (num_idles fol)}, pos)
    moveOvershoot n dmv = (fol{overshooting=Just (n-1)}, addR2 pos dmv)
    stayIdle 0 = (fol{idling=Nothing}, pos)
    stayIdle n = (fol{idling=Just (n-1)}, pos)
    listenForMessage = let getloc (ISawHim loc) = loc in (fol{holyPlace = majorityVote $ map getloc messages}, pos)

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
