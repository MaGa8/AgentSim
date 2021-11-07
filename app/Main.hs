{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Lib
import qualified Messiah as M

import qualified Data.Map as Map
import Data.Bifunctor

import Control.Monad.State

import System.Random as R

type V = M.R2
type M = M.Message
type A = M.AgentData
type Instance = Agent V M A
type Iterations = Int

main :: IO ()
main = do
  -- let mkAgents = (++) <$> mkFollowers 100 <*> mkMessiah 1
  -- agents <- getStdRandom (runState mkAgents)
  -- positions <- getStdRandom (runState (mkPositions (0,100) (0,100) 100))
  gen <- getStdGen
  let agents = uncurry initPositions . first (\funs -> zipWith ($) funs [1 ..]) $ evalState (mkAgents 1 10) gen
  withVis (conductSim agents 500 20) "Messiah Game" (1200,960) (floor fieldMaxX, floor fieldMaxY)

fieldMinX, fieldMinY, fieldMaxX, fieldMaxY :: Double
fieldMinX = 0
fieldMinY = 0
fieldMaxX = 100
fieldMaxY = 100

veloMax :: Double
veloMax = 2
  
mkAgents :: (R.RandomGen g) => Int -> Int -> State g ([M.Uid -> Instance], [V])
mkAgents nmessiah nfollower = do
  messiahs <- replicateM nmessiah (reorder M.messiah <$> return 100 <*> genMove <*> genMessiah)
  followers <- replicateM nfollower (reorder M.follower <$> return 25 <*> genMove <*> genFollower)
  pos <- replicateM (nmessiah + nfollower) genPosition
  return (messiahs ++ followers, pos)
  where
    reorder f viewRange move kind uid = f uid viewRange move kind
    -- genViewRange = state (\gen -> let maxRange = max (fieldMaxX - fieldMinX) (fieldMaxY - fieldMinY)
                                  -- in R.randomR (0, maxRange) gen)
    genMove = (\v -> M.Move{ M.velocity = v }) <$> genVector veloMax
    genMessiah = M.Messiah ((fieldMinX,fieldMinY), (fieldMaxX,fieldMaxY)) <$> genCoord Nothing <*> state (first mkStdGen . random)
    genFollower = return $ M.Follower Nothing
    genPosition = genCoord Nothing

genCoord :: (R.RandomGen g, MonadState g m) => Maybe (M.R2, M.R2) -> m M.R2
genCoord mbounds = (,) <$> state (randomR xbound) <*> state (randomR ybound)
  where
    xbound = maybe (fieldMinX,fieldMaxX) fst mbounds
    ybound = maybe (fieldMinY,fieldMaxY) snd mbounds

genVector :: (R.RandomGen g, MonadState g m) => Double -> m M.R2
genVector maxNorm = do
  norm <- state (randomR (0, maxNorm))
  angle <- state (randomR (0, 2*pi))
  return (cos angle * norm, sin angle * norm)

logicStates :: Map Instance V -> [Map Instance V]
logicStates agents = let agents' = sim M.comparatorSeq agents in agents' : logicStates agents'

conductSim :: Map Instance V -> Iterations -> Fps -> Window -> RendIO (Map Instance V)
conductSim agents niter fps win = fmap last . mapM (\agentState -> renderToScreen agentState >> return agentState) . take niter $ logicStates agents
  where
    renderToScreen agents' = throttle fps . drawScene . map (uncurry M.appear) $ Map.toList agents'
      

-- conductSim agents 0 _ _ = return agents
-- conductSim agents niter fps win = let agents' = sim M.comparatorSeq agents
                                  -- in drawScene (map (uncurry M.appear) $ Map.toList agents') >> conductSim agents' (niter - 1) win
