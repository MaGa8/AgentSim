{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}

module Agent
  (
    Agent(..), Neighbor, Speech, Behavior, Sight
  , agentTalk, agentAct, agentSee
  , updateCore, updatePos
  ) where

import Data.Map as M

type Neighbor d a p = (d,a,p)
type Speech d p m a = forall t. p -> a -> t (Neighbor d a p) -> [(d,m)]
type Behavior p m a = p -> a -> [m] -> (a,p)
type Sight p a = p -> a -> (p,p)

data Agent d p m a = Agent{ talk :: Speech d p m a, act :: Behavior p m a, see :: Sight p a, core :: a, getIdent :: d, getPos :: p }

instance (Eq a) => Eq (Agent d p m a) where
  a1 == a2 = core a1 == core a2

instance (Ord a) => Ord (Agent d p m a) where
  compare a1 a2 = compare (core a1) (core a2)

agentTalk :: (Foldable t) => Agent d p m a -> t (d,a,p) -> [(d,m)]
agentTalk ag = talk ag (getPos ag) (core ag)

agentAct :: Agent d p m a -> [m] -> (a,p)
agentAct ag = act ag (getPos ag) (core ag)

agentSee :: Agent d p m a -> (p,p)
agentSee ag = see ag (getPos ag) (core ag)

updateCore :: Agent d p m a -> a -> Agent d p m a
updateCore ag c = ag{ core = c }

updatePos :: Agent d p m a -> p -> Agent d p m a
updatePos ag pos = ag{ getPos = pos }
