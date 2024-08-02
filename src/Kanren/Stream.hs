{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Kanren.Stream (
  StreamT (..),
  done,
  await,
  maybeToStream,
  maybeToStreamM,
  mapM,
  interleave,
  toList,
  fuseAwaits,
  observeAll,
  observeMany,
) where

import Data.Maybe (catMaybes)
import Control.Applicative (Alternative(..))
import Control.Monad (ap)
import Prelude hiding (take, mapM)

import Streamly.Data.StreamK (StreamK)
import qualified Streamly.Data.Stream as Stream
import qualified Streamly.Data.StreamK as StreamK
import qualified Streamly.Data.Fold as Fold

newtype StreamT m a = StreamT { runStreamT :: StreamK m (Maybe a) }
  deriving (Functor)

done :: Monad m => StreamT m a
done = empty

await :: Monad m => m (StreamT m a) -> StreamT m a
await ys = StreamT $ StreamK.fromPure Nothing `StreamK.append` StreamK.concatEffect (runStreamT <$> ys)

instance Monad m => Applicative (StreamT m) where
  pure = StreamT . StreamK.fromPure . Just
  (<*>) = ap

instance Monad m => Alternative (StreamT m) where
  empty = StreamT StreamK.nil
  StreamT xs <|> StreamT ys = StreamT (xs `StreamK.append` ys)

instance Monad m => Monad (StreamT m) where
  StreamT xs >>= f = StreamT $ flip (StreamK.concatMapWith StreamK.interleave) xs $ \case
    Nothing -> StreamK.fromPure Nothing
    Just x -> runStreamT (f x)

maybeToStream :: Maybe a -> StreamT m a
maybeToStream Nothing = StreamT StreamK.nil
maybeToStream (Just x) = StreamT (StreamK.fromPure (Just x))

maybeToStreamM :: Monad m => m (Maybe a) -> StreamT m a
maybeToStreamM = StreamT . StreamK.fromEffect

interleave :: StreamT m a -> StreamT m a -> StreamT m a
interleave (StreamT xs) (StreamT ys) = StreamT (xs `StreamK.interleave` ys)

observeAll :: Monad m => StreamT m a -> m [a]
observeAll (StreamT xs) = catMaybes <$> Stream.fold Fold.toList (StreamK.toStream xs)

observeMany :: Monad m => Int -> StreamT m a -> m [a]
observeMany n xs = Stream.fold Fold.toList (StreamK.toStream (StreamK.take n (fuseAwaits xs)))

toList :: (Monad m) => (a -> m b) -> StreamT m a -> m [b]
toList f xs = do
  ys <- observeAll xs
  traverse f ys

fuseAwaits :: StreamT m a -> StreamK m a
fuseAwaits (StreamT xs) = StreamK.concatMapWith StreamK.append k xs
  where
    k Nothing = StreamK.nil
    k (Just x) = StreamK.fromPure x

mapM :: Monad m => (a -> m b) -> StreamT m a -> StreamT m b
mapM f (StreamT xs) = StreamT (StreamK.mapM (traverse f) xs)
