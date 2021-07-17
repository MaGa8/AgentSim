{-# LANGUAGE MultiParamTypeClasses #-}

module Agent
  (
    Agent
  ) where

class Agent a i v m where
  trans :: a i v m -> a i v m
  talk :: (Foldable t) => a i v m -> t i -> [(i,m)]
  listen :: (Foldable t) => a i v m -> t (i,m) -> a i v m
  locate :: a i v m -> v
  index :: a i v m -> i

  
  
