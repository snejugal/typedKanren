{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Kanren.Stream (
  StreamT (..),
  done,
  await,
  maybeToStream,
  maybeToStreamM,
  interleave,
  toList,
  fuseAwaits,
  observeAll,
  observeMany,
) where

import Data.Maybe (catMaybes)
import Control.Applicative (Alternative(..))
import Control.Monad.Logic (LogicT)
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad (ap)
import Prelude hiding (take)

newtype StreamT m a = StreamT { runStreamT :: LogicT m (Maybe a) }
  deriving (Functor)

done :: Monad m => StreamT m a
done = empty

await :: Monad m => m (StreamT m a) -> StreamT m a
await ys = StreamT $ pure Nothing <|> do
  lift ys >>= runStreamT

instance Monad m => Applicative (StreamT m) where
  pure = StreamT . pure . Just
  (<*>) = ap

instance Monad m => Alternative (StreamT m) where
  empty = StreamT empty
  StreamT xs <|> StreamT ys = StreamT (xs <|> ys)

instance Monad m => Monad (StreamT m) where
  StreamT xs >>= f = StreamT $ xs >>= \case
    Nothing -> pure Nothing
    Just x -> runStreamT (f x)

maybeToStream :: Maybe a -> StreamT m a
maybeToStream Nothing = StreamT empty
maybeToStream (Just x) = StreamT (pure (Just x))

maybeToStreamM :: Monad m => m (Maybe a) -> StreamT m a
maybeToStreamM m = StreamT $ do
  lift m >>= \case
    Nothing -> empty
    Just x -> pure (Just x)

interleave :: Monad m => StreamT m a -> StreamT m a -> StreamT m a
interleave (StreamT xs) (StreamT ys) = StreamT (xs `Logic.interleave` ys)

observeAll :: Applicative m => StreamT m a -> m [a]
observeAll (StreamT xs) = catMaybes <$> Logic.observeAllT xs

observeMany :: Monad m => Int -> StreamT m a -> m [a]
observeMany n xs = Logic.observeManyT n (fuseAwaits xs)

toList :: (Monad m) => (a -> m b) -> StreamT m a -> m [b]
toList f (StreamT xs) = do
  ys <- catMaybes <$> Logic.observeAllT xs
  traverse f ys

fuseAwaits :: StreamT m a -> LogicT m a
fuseAwaits (StreamT xs) = do
  xs >>= \case
    Nothing -> empty
    Just x -> pure x