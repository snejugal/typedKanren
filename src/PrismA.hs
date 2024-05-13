{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PrismA (
  PrismA (..),
  Just',
  Nothing',
  Left',
  Right',
  reviewA,
  previewA,
  matchingA,
) where

import Control.Lens

class PrismA p a b where
  type Source p a
  make :: p -> Prism (Source p a) (Source p b) a b

data p :. q = p :. q

instance (PrismA p (Source q a) (Source q b), PrismA q a b) => PrismA (p :. q) a b where
  type Source (p :. q) a = Source p (Source q a)
  make (l :. p) = make l . make p

data Just' = Just'
data Nothing' a = Nothing'

instance PrismA Just' a b where
  type Source Just' a = Maybe a
  make Just' = _Just

instance PrismA (Nothing' a) () () where
  type Source (Nothing' a) () = Maybe a
  make Nothing' = _Nothing

data Left' b = Left'
data Right' a = Right'

instance PrismA (Left' b) a c where
  type Source (Left' b) a = Either a b
  make Left' = _Left

instance PrismA (Right' a) b c where
  type Source (Right' a) b = Either a b
  make Right' = _Right

reviewA :: (PrismA p a a) => p -> a -> Source p a
reviewA = review . make

previewA :: (PrismA p a a) => p -> Source p a -> Maybe a
previewA = preview . make

matchingA :: forall a b p. (PrismA p a b) => p -> Source p a -> Either (Source p b) a
matchingA = matching . make @p @a @b
