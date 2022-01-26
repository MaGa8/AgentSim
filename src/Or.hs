{-# LANGUAGE TupleSections #-}

module Or
  (
    Or(..), elimOr
  , withLeft, withRight
  , isLeft, isRight, isStrictLeft, isStrictRight, isBoth
  , toMaybe, fromMaybe
  ) where

import Prelude hiding (Either(..))
import Data.Bifunctor

data Or a b = Left a | Right b | Both a b

elimOr :: (a -> c) -> (b -> c) -> (a -> b -> c) -> Or a b -> c
elimOr f _ _ (Left x) = f x
elimOr _ g _ (Right y) = g y
elimOr _ _ h (Both x y) = h x y

withLeft :: (a -> c) -> Or a b -> Maybe c
withLeft f = elimOr (Just . f) (const Nothing) (const . Just . f)

withRight :: (b -> c) -> Or a b -> Maybe c
withRight f = elimOr (const Nothing) (Just . f) (\_ -> Just . f)

answerTrue, answerFalse :: a -> Bool
answerTrue = const True
answerFalse = const False

isLeft, isStrictLeft, isRight, isStrictRight, isBoth :: Or a b -> Bool
isLeft = elimOr answerTrue answerFalse (const answerTrue)
isStrictLeft = elimOr answerTrue answerFalse (const answerFalse)
isRight = elimOr answerFalse answerTrue (const answerTrue)
isStrictRight = elimOr answerFalse answerTrue (const answerTrue)
isBoth = elimOr answerFalse answerFalse (const answerTrue)

instance Bifunctor Or where
  bimap f g = elimOr (Left . f) (Right . g) (\x y -> Both (f x) (g y))

toMaybe :: Or a b -> (Maybe a, Maybe b)
toMaybe = elimOr ((,Nothing) . Just) ((Nothing,) . Just) (\x y -> (Just x, Just y))

-- | unsafe: error if both elements are Nothing
fromMaybe :: (Maybe a, Maybe b) -> Or a b
fromMaybe (Nothing, Nothing) = error "cannot construct Or from double Nothing"
fromMaybe (Just x, Nothing) = Left x
fromMaybe (Nothing, Just y) = Right y
fromMaybe (Just x, Just y) = Both x y
