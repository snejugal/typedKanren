{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Biprism (Biprism, biprism, reviewl, reviewr, matching) where

import Control.Lens (Choice (right'), dimap)
import Data.Biapplicative (Biapplicative (bipure, (<<*>>)))
import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Functor.Const (Const (Const, getConst))
import Data.Tagged (Tagged (Tagged, unTagged))

type Biprism s t a b =
  forall p f
   . (Choice p, Biapplicative f)
  => p a (f a b)
  -> p s (f s t)

biprism :: (a -> s) -> (b -> t) -> (s -> Either t a) -> Biprism s t a b
biprism setl setr get = dimap get' set' . right'
 where
  get' x = first (x,) (get x)
  set' (Right fab) = bimap setl setr fab
  set' (Left (s, t)) = bipure s t

reviewl :: Biprism s t a b -> a -> s
reviewl p = getConst . unTagged . p . Tagged . Const

reviewr :: Biprism s t a b -> b -> t
reviewr p = unTagged . unTagged . p . Tagged . Tagged

data Either' a b c
  = Left' a
  | Right' b c

instance Functor (Either' a b) where
  fmap = bimap id

instance Bifunctor (Either' a) where
  bimap _ _ (Left' a) = Left' a
  bimap f g (Right' b c) = Right' (f b) (g c)

instance Biapplicative (Either' a) where
  bipure = Right'

  Left' a <<*>> _ = Left' a
  _ <<*>> Left' a = Left' a
  Right' f g <<*>> Right' b c = Right' (f b) (g c)

matching :: Biprism s t a b -> s -> Either t a
matching p x = case p Left' x of
  Left' a -> Right a
  Right' _ t -> Left t
