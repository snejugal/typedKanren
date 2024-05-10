{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Biprism (Biprism, biprism, toPrism, fromPrisms, reviewl, reviewr, matching) where

import Control.Lens (Choice (right'), Prism, Prism', Profunctor (rmap), dimap)
import Control.Lens.Review (review, reviewing)
import Data.Biapplicative (Biapplicative (bipure, (<<*>>)))
import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Bifunctor.Joker (Joker (Joker, runJoker))
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

toPrism :: Biprism s t a b -> Prism s t a b
toPrism b = rmap runJoker . b . rmap Joker

fromPrisms :: Prism' s a -> Prism s t a b -> Biprism s t a b
fromPrisms l r = biprism (set l) (set r) get
 where
  set p = review (reviewing p)
  get = either Right Left . r Left

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
