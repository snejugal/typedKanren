{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Kanren.Stream (
  StreamT (..),
  maybeToStream,
  interleave,
  toList,
  take,
) where

import Control.Monad (ap)
import Data.Functor ((<&>))
import Prelude hiding (take)

data StreamT m a
  = Done
  | Only a
  | Yield a (StreamT m a)
  | Await (m (StreamT m a))
  | M (m (StreamT m a))
  deriving (Functor)

instance (Monad m) => Applicative (StreamT m) where
  pure = Only
  (<*>) = ap

instance (Monad m) => Monad (StreamT m) where
  Done >>= _ = Done
  Only x >>= f = f x
  Yield x xs >>= f = interleave (f x) (xs >>= f)
  Await xs >>= f = Await (reduceM (xs <&> (>>= f)))
  M xs >>= f = M (reduceM (xs <&> (>>= f)))

reduceM :: (Monad m) => m (StreamT m a) -> m (StreamT m a)
reduceM xs =
  xs >>= \case
    M inner -> inner
    other -> return other

maybeToStream :: Maybe a -> StreamT m a
maybeToStream Nothing = Done
maybeToStream (Just x) = Only x

interleave :: (Applicative m) => StreamT m a -> StreamT m a -> StreamT m a
interleave Done ys = ys
interleave (Only x) ys = Yield x ys
interleave (Yield x xs) ys = Yield x (interleave ys xs)
interleave (Await xs) ys = Await (interleave ys <$> xs)
interleave (M xs) ys = M (xs <&> (`interleave` ys))

toList :: (Monad m) => (a -> m b) -> StreamT m a -> m [b]
toList _ Done = pure []
toList f (Only x) = f x <&> (: [])
toList f (Yield x xs) = do
  x' <- f x
  xs' <- toList f xs
  return (x' : xs')
toList f (Await xs) = xs >>= toList f
toList f (M xs) = xs >>= toList f

take :: (Functor m) => Int -> StreamT m a -> StreamT m a
take n _ | n <= 0 = Done
take _ Done = Done
take _ (Only x) = Only x
take n (Yield x xs) = Yield x (take (n - 1) xs)
take n (Await xs) = Await (take n <$> xs)
take n (M xs) = M (take n <$> xs)
