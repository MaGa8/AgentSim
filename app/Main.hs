
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Lib
import qualified Instances.Messiah as M

import qualified Data.Map as Map
import Data.Bifunctor

import Control.Monad.State

import System.Random as R

import Debug.Trace

type V = M.R2
type M = M.Message
type A = M.AgentData
type Instance = M.Instance
type Iterations = Int

main :: IO ()
main = do
  -- let mkAgents = (++) <$> mkFollowers 100 <*> mkMessiah 1
  -- agents <- getStdRandom (runState mkAgents)
  -- positions <- getStdRandom (runState (mkPositions (0,100) (0,100) 100))
  gen <- getStdGen
  let agents = (\funs -> zipWith ($) funs [1 ..]) $ evalState (mkAgents 5 5000) gen
  withVis (conductSim agents 1000 15) "Messiah Game" (1200,960) (floor fieldMaxX, floor fieldMaxY)

fieldMinX, fieldMinY, fieldMaxX, fieldMaxY :: Double
fieldMinX = 0
fieldMinY = 0
fieldMaxX = 200
fieldMaxY = 200

followVeloMin, followVeloMax, messiahVeloMin, messiahVeloMax  :: Double
followVeloMin = 1
followVeloMax = 7
messiahVeloMin = 2
messiahVeloMax = 3

  
mkAgents :: (R.RandomGen g) => Int -> Int -> State g [M.Uid -> Instance]
mkAgents nmessiah nfollower = do
  messiahs <- replicateM nmessiah (reorder M.messiah <$> return 15 <*> genMessiahMove <*> genCoord Nothing <*> genMessiah)
  followers <- replicateM nfollower (reorder M.follower <$> return 7 <*> genFollowerMove <*> genCoord Nothing <*> genFollower)
  return (messiahs ++ followers)
  where
    reorder f viewRange move pos kind uid = f uid viewRange move pos kind
    -- genViewRange = state (\gen -> let maxRange = max (fieldMaxX - fieldMinX) (fieldMaxY - fieldMinY)
                                  -- in R.randomR (0, maxRange) gen)
    genMessiahMove = (\v -> M.Move{ M.velocity = v }) <$> state (randomR (messiahVeloMin, messiahVeloMax))
    genFollowerMove = (\v -> M.Move{ M.velocity = v }) <$> state (randomR (followVeloMin, followVeloMax))
    genMessiah = M.Messiah ((fieldMinX,fieldMinY), (fieldMaxX,fieldMaxY)) <$> genCoord Nothing <*> state (first mkStdGen . random)
    genFollower = return $ M.initFollower 15 30

genCoord :: (R.RandomGen g, MonadState g m) => Maybe (M.R2, M.R2) -> m M.R2
genCoord mbounds = (,) <$> state (randomR xbound) <*> state (randomR ybound)
  where
    xbound = maybe (fieldMinX,fieldMaxX) fst mbounds
    ybound = maybe (fieldMinY,fieldMaxY) snd mbounds

genVector :: (R.RandomGen g, MonadState g m) => Double -> Double -> m M.R2
genVector minNorm maxNorm = do
  norm <- state (randomR (minNorm, maxNorm))
  angle <- state (randomR (0, pi))
  return (cos angle * norm, sin angle * norm)

logicStates :: [Instance] -> [[Instance]]
-- logicStates agents = let agents' = simDebug M.debugMessages M.debugAgent M.comparatorSeq agents in agents' : logicStates agents'
logicStates agents = let agents' = sim M.comparatorSeq agents in agents' : logicStates agents'

conductSim :: [Instance] -> Iterations -> Fps -> Window -> RendIO [Instance]
conductSim agents niter fps win = fmap last . mapM (\agentState -> renderToScreen agentState >> return agentState) . take niter $ logicStates agents
  where
    renderToScreen agents' = throttleDebug fps . drawScene . map M.appear $ agents'
      

-- conductSim agents 0 _ _ = return agents
-- conductSim agents niter fps win = let agents' = sim M.comparatorSeq agents
                                  -- in drawScene (map (uncurry M.appear) $ Map.toList agents') >> conductSim agents' (niter - 1) win
