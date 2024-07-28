{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | 'Generic' implementations of 'Logical' methods.
--
-- As discussed in the documentation for the 'Logical' class, method
-- implementations are not particularly interesting and can be easily
-- automated. This module provides such automated implementations using
-- 'Generic'.
--
-- This module expects that you already have a logical representation for your
-- type, and there's already a 'Logic' type instance. The logical type must not
-- change the order of constructors as well as the order of fields in each
-- constructor, but the names do not matter. Additionally, each field in the
-- original type must be wrapped in a 'Term' in the logical representation.
--
-- For example, consider the following type definition:
--
-- > data Tree a
-- >   = Leaf a
-- >   | Node (Tree a) (Tree a)
-- >   deriving (Generic)
-- >
-- > data LogicTree a
-- >   = LogicLeaf (Term a)
-- >   | LogicNode (Term (Tree a)) (Term (Tree a))
-- >   deriving (Generic)
--
-- From there, using the generic implementations is trivial:
--
-- > instance (Logical a) => Logical (Tree a) where
-- >   type Logic (Tree a) = LogicTree a
-- >   unify = genericUnify
-- >   subst = genericSubst
-- >   inject = genericInject
-- >   extract = genericExtract
module Kanren.GenericLogical (
  genericUnify,
  genericWalk,
  genericOccursCheck,
  genericInject,
  genericExtract,
  GLogical,
) where

import Control.Monad.ST.Strict (ST)
import Data.Proxy (Proxy (..))
import GHC.Generics

import Kanren.Core

class GLogical s f f' where
  gunify :: Proxy f -> f' p -> f' p -> State s -> ST s (Maybe (State s))
  gwalk :: Proxy f -> State s -> f' p -> ST s (f' p)
  goccursCheck :: Proxy f -> Var s b -> f' p -> State s -> ST s Bool
  ginject :: Proxy s -> f p -> f' p
  gextract :: Proxy s -> f' p -> Maybe (f p)

instance GLogical s V1 V1 where
  gunify _ _ _ = return . Just
  gwalk _ _ = return
  goccursCheck _ _ _ _ = return False
  ginject _ = id
  gextract _ = Just

instance GLogical s U1 U1 where
  gunify _ _ _ = return . Just
  gwalk _ _ = return
  goccursCheck _ _ _ _ = return False
  ginject _ = id
  gextract _ = Just

instance (GLogical s f f', GLogical s g g') => GLogical s (f :+: g) (f' :+: g') where
  gunify _ (L1 x) (L1 y) = gunify (Proxy @f) x y
  gunify _ (R1 x) (R1 y) = gunify (Proxy @g) x y
  gunify _ _ _ = const (return Nothing)

  gwalk _ k (L1 x) = L1 <$> gwalk (Proxy @f) k x
  gwalk _ k (R1 y) = R1 <$> gwalk (Proxy @g) k y

  goccursCheck _ varId (L1 x) = goccursCheck (Proxy @f) varId x
  goccursCheck _ varId (R1 y) = goccursCheck (Proxy @g) varId y

  ginject _ (L1 x) = L1 (ginject (Proxy @s) x)
  ginject _ (R1 y) = R1 (ginject (Proxy @s) y)

  gextract _ (L1 x) = L1 <$> gextract (Proxy @s) x
  gextract _ (R1 y) = R1 <$> gextract (Proxy @s) y

instance (GLogical s f f', GLogical s g g') => GLogical s (f :*: g) (f' :*: g') where
  gunify _ (x1 :*: y1) (x2 :*: y2) state =
    gunify (Proxy @f) x1 x2 state >>= \case
      Nothing -> return Nothing
      Just state' -> gunify (Proxy @g) y1 y2 state'
  gwalk _ k (x :*: y) = (:*:) <$> gwalk (Proxy @f) k x <*> gwalk (Proxy @g) k y
  goccursCheck _ varId (x :*: y) state = do
    occursX <- goccursCheck (Proxy @f) varId x state
    occursY <- goccursCheck (Proxy @g) varId y state
    return (occursX || occursY)
  ginject _ (x :*: y) = ginject (Proxy @s) x :*: ginject (Proxy @s) y
  gextract _ (x :*: y) = do
    x' <- gextract (Proxy @s) x
    y' <- gextract (Proxy @s) y
    return (x' :*: y')

instance (Logical c) => GLogical s (K1 i c) (K1 i' (Term s c)) where
  gunify _ (K1 x) (K1 y) = unify' x y
  gwalk _ state (K1 c) = K1 <$> walk' state c
  goccursCheck _ varId (K1 c) = occursCheck' varId c
  ginject _ (K1 x) = K1 (inject' x)
  gextract _ (K1 x) = K1 <$> extract' x

instance (GLogical s f f') => GLogical s (M1 i t f) (M1 i' t' f') where
  gunify _ (M1 x) (M1 y) = gunify (Proxy @f) x y
  gwalk _ k (M1 m) = M1 <$> gwalk (Proxy @f) k m
  goccursCheck _ varId (M1 m) = goccursCheck (Proxy @f) varId m
  ginject _ (M1 x) = M1 (ginject (Proxy @s) x)
  gextract _ (M1 x) = M1 <$> gextract (Proxy @s) x

-- | The generic implementation of 'unify'.
genericUnify
  :: forall a s
   . (Generic (Logic s a), GLogical s (Rep a) (Rep (Logic s a)))
  => Logic s a
  -> Logic s a
  -> State s
  -> ST s (Maybe (State s))
genericUnify l r = gunify (Proxy @(Rep a)) (from l) (from r)

-- | The generic implementation of 'walk'.
genericWalk
  :: forall a s
   . (Generic (Logic s a), GLogical s (Rep a) (Rep (Logic s a)))
  => State s
  -> Logic s a
  -> ST s (Logic s a)
genericWalk k term = to <$> gwalk (Proxy @(Rep a)) k (from term)

-- | The generic implementation of 'walk'.
genericOccursCheck
  :: forall a b s
   . (Generic (Logic s a), GLogical s (Rep a) (Rep (Logic s a)))
  => Var s b
  -> Logic s a
  -> State s
  -> ST s Bool
genericOccursCheck varId term = goccursCheck (Proxy @(Rep a)) varId (from term)

-- | The generic implementation of 'inject'.
genericInject
  :: forall a s
   . (Generic a, Generic (Logic s a), GLogical s (Rep a) (Rep (Logic s a)))
  => a
  -> Logic s a
genericInject x = to (ginject (Proxy @s) (from x))

-- | The generic implementation of 'extract'.
genericExtract
  :: forall a s
   . (Generic a, Generic (Logic s a), GLogical s (Rep a) (Rep (Logic s a)))
  => Logic s a
  -> Maybe a
genericExtract x = to <$> gextract (Proxy @s) (from x)
