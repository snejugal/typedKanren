{-# LANGUAGE DeriveTraversable #-}

module Kanren.Stream (
  Stream (..),
  maybeToStream,
  interleave,
  STStream (..),
  interleaveSTStream,
) where

import Control.Monad.ST (ST)
import Prelude hiding (take)

data Stream a
  = Done
  | Only a
  | Yield a (Stream a)
  | Await (Stream a)
  deriving (Functor, Foldable, Traversable)

instance (Show a) => Show (Stream a) where
  show ys = "[" ++ show' ys
   where
    show' Done = "]"
    show' (Only x) = show x ++ "]"
    show' (Yield x xs@(Yield _ _)) = show x ++ ", " ++ show' xs
    show' (Yield x xs) = show x ++ show' xs
    show' (Await xs) = show xs -- FIXME: demonstrate the use of Await

instance Applicative Stream where
  pure = Only

  Done <*> _ = Done
  Only f <*> xs = fmap f xs
  Yield f fs <*> xs = interleave (fmap f xs) (fs <*> xs)
  Await fs <*> xs = Await (fs <*> xs)

instance Monad Stream where
  Done >>= _ = Done
  Only x >>= f = f x
  Yield x xs >>= f = interleave (f x) (xs >>= f)
  Await xs >>= f = Await (xs >>= f)

maybeToStream :: Maybe a -> Stream a
maybeToStream Nothing = Done
maybeToStream (Just x) = pure x

interleave :: Stream a -> Stream a -> Stream a
interleave Done ys = ys
interleave (Only x) ys = Yield x ys
interleave (Yield x xs) ys = Yield x (interleave ys xs)
interleave (Await xs) ys = Await (interleave ys xs)

newtype STStream s a = STStream {runSTStream :: ST s (Stream a)}
  deriving (Functor)

instance Applicative (STStream s) where
  pure = STStream . pure . pure

  STStream left <*> STStream right = STStream $ do
    left' <- left
    right' <- right
    return (left' <*> right')

instance Monad (STStream s) where
  (STStream stream) >>= f = STStream (stream >>= go)
   where
    go Done = return Done
    go (Only x) = runSTStream (f x)
    go (Yield x xs) = interleave <$> runSTStream (f x) <*> go xs
    go (Await xs) = Await <$> go xs

interleaveSTStream :: STStream s a -> STStream s a -> STStream s a
interleaveSTStream (STStream left) (STStream right) = STStream (interleave <$> left <*> right)
