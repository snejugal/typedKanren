{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor  #-}

module Kanren.Stream (Stream (..), maybeToStream, interleave) where

import           Prelude hiding (take)

data Stream a
  = Done
  | Yield a (Stream a)
  | Await (Stream a)
  deriving (Functor, Foldable)

instance (Show a) => Show (Stream a) where
  show ys = "[" ++ show' ys
   where
    show' Done                     = "]"
    show' (Yield x xs@(Yield _ _)) = show x ++ ", " ++ show' xs
    show' (Yield x xs)             = show x ++ show' xs
    show' (Await xs)               = show xs    -- FIXME: demonstrate the use of Await

instance Applicative Stream where
  pure x = Yield x Done

  Done <*> _        = Done
  Yield f fs <*> xs = interleave (fmap f xs) (fs <*> xs)
  Await fs <*> xs   = Await (fs <*> xs)

instance Monad Stream where
  Done >>= _       = Done
  Yield x xs >>= f = interleave (f x) (xs >>= f)
  Await xs >>= f   = Await (xs >>= f)

maybeToStream :: Maybe a -> Stream a
maybeToStream Nothing  = Done
maybeToStream (Just x) = pure x

interleave :: Stream a -> Stream a -> Stream a
interleave Done ys         = ys
interleave (Yield x xs) ys = Yield x (interleave ys xs)
interleave (Await xs) ys   = Await (interleave ys xs)
