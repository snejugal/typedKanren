{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE RankNTypes     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use foldr" #-}

module Kanren.Stream (Stream (..), maybeToStream, interleave, delayStream, emptyStream, toStream) where

import           Control.Monad (ap)
import           Prelude       hiding (take)

newtype Stream a = Stream { unStream :: forall r. (a -> r -> r) -> (r -> r) -> r -> r }
  deriving (Functor)

instance Foldable Stream where
  foldr f z (Stream k) = k f id z

instance Applicative Stream where
  pure x = Stream (\yield _await done -> yield x done)

  (<*>) = ap
  -- Done <*> _        = Done
  -- Yield f fs <*> xs = interleave (fmap f xs) (fs <*> xs)
  -- Await fs <*> xs   = Await (fs <*> xs)

instance Monad Stream where
  Stream kx >>= f = Stream $ \yield await done -> kx
    (\x xs -> unStream (f x) yield await xs)
    (\xs -> await xs)
    done

-- instance Monad Stream where
--   Done >>= _       = Done
--   Yield x xs >>= f = interleave (f x) (xs >>= f)
--   Await xs >>= f   = Await (xs >>= f)

maybeToStream :: Maybe a -> Stream a
maybeToStream Nothing  = emptyStream
maybeToStream (Just x) = pure x

interleave :: Stream a -> Stream a -> Stream a
interleave xs ys = toStream' (interleave' (fromStream' xs) (fromStream' ys))
-- interleave xs ys =
--   case splitStream xs of
--     Just (Just x, xs') -> Stream $ \yield await done ->
--       yield x (unStream (interleave ys xs') yield await done)
--     Just (Nothing, xs') -> Stream $ \yield await done ->
--       await (unStream (interleave ys xs') yield await done)
--     Nothing -> ys

splitStream :: Stream a -> Maybe (Maybe a, Stream a)
splitStream (Stream k) = snd $ k
  (\x (xs, _) -> (Stream (\yield await done -> yield x (unStream xs yield await done)), Just (Just x, xs)))
  (\(xs, _) -> (Stream (\yield await done -> await (unStream xs yield await done)), Just (Nothing, xs)))
  (emptyStream, Nothing)

-- interleave :: Stream a -> Stream a -> Stream a
-- interleave Done ys         = ys
-- interleave (Yield x xs) ys = Yield x (interleave ys xs)
-- interleave (Await xs) ys   = Await (interleave ys xs)

delayStream :: Stream a -> Stream a
delayStream (Stream k) = Stream $ \yield await done ->
  await (k yield await done)

emptyStream :: Stream a
emptyStream = Stream (\_yield _await done -> done)

toStream :: [a] -> Stream a
toStream xs = Stream $ \yield _await done ->
  foldr yield done xs

toStream' :: [Maybe a] -> Stream a
toStream' xs = Stream $ \yield await done ->
  foldr (maybe await yield) done xs

fromStream' :: Stream a -> [Maybe a]
fromStream' (Stream k) = k
  (\x xs -> Just x : xs)
  (\xs -> Nothing : xs)
  []

interleave' :: [a] -> [a] -> [a]
interleave' (x:xs) (y:ys) = x : y : interleave' xs ys
interleave' [] ys         = ys
interleave' xs []         = xs
