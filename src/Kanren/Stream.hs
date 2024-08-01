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
  take,
) where

import Data.Maybe (catMaybes)
import Control.Applicative (Alternative(..))
import Control.Monad.Logic (LogicT)
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.Logic as Logic
import Control.Monad (ap, join, MonadPlus(..))
import Data.Functor ((<&>))
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
  StreamT fs <*> StreamT xs = StreamT $
    liftA2 (<*>) fs xs

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

toList :: (Monad m) => (a -> m b) -> StreamT m a -> m [b]
toList f (StreamT xs) = do
  ys <- catMaybes <$> Logic.observeAllT xs
  traverse f ys

fuseAwaits :: (Monad m) => StreamT m a -> LogicT m a
fuseAwaits (StreamT xs) = do
  Logic.msplit xs >>= \case
    Nothing -> empty
    Just (Nothing, ys) -> fuseAwaits (StreamT ys)
    Just (Just y, ys) -> pure y <|> fuseAwaits (StreamT ys)

take :: (Monad m) => Int -> StreamT m a -> StreamT m a
take n (StreamT xs)
  | n <= 0 = empty
  | otherwise = StreamT $ do
      Logic.msplit xs >>= \case
        Nothing -> empty
        Just (Nothing, ys) -> runStreamT (take n (StreamT ys))
        Just (Just y, ys) -> runStreamT (pure y <|> take (n - 1) (StreamT ys))