{-# LANGUAGE MultiParamTypeClasses #-}

module Agent
  (
    Agent(..), Speech, Behavior, Sight
  , agentTalk, agentAct, agentSee
  , updateCore
  ) where

import Data.Map as M

type Speech p m a = p -> a -> Map a p -> Map a m
type Behavior p m a = p -> a -> [m] -> (a,p)
type Sight p a = p -> a -> (p,p)

data Agent p m a = Agent{ talk :: Speech p m a, act :: Behavior p m a, see :: Sight p a, core :: a }

instance (Eq a) => Eq (Agent p m a) where
  a1 == a2 = core a1 == core a2

instance (Ord a) => Ord (Agent p m a) where
  compare a1 a2 = compare (core a1) (core a2)

agentTalk :: Agent p m a -> p -> Map a p -> Map a m
agentTalk ag pos = talk ag pos (core ag)

agentAct :: Agent p m a -> p -> [m] -> (a,p)
agentAct ag pos = act ag pos (core ag)

agentSee :: Agent p m a -> p -> (p,p)
agentSee ag pos = see ag pos (core ag)

updateCore :: Agent p m a -> a -> Agent p m a
updateCore ag c = ag{ core = c }
