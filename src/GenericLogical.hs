{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
module GenericLogical (
  genericUnify,
  genericWalk,
  genericInject,
  genericExtract,
  GLogical,
) where

import Control.Monad ((>=>))
import Data.Proxy (Proxy (..))
import GHC.Generics

import Core

class GLogical f f' where
  gunify :: Proxy f -> f' p -> f' p -> State -> Maybe State
  gwalk :: Proxy f -> State -> f' p -> f' p
  ginject :: f p -> f' p
  gextract :: f' p -> Maybe (f p)

instance GLogical V1 V1 where
  gunify _ _ _ = Just
  gwalk _ _ = id
  ginject = id
  gextract = Just

instance GLogical U1 U1 where
  gunify _ _ _ = Just
  gwalk _ _ = id
  ginject = id
  gextract = Just

instance (GLogical f f', GLogical g g') => GLogical (f :+: g) (f' :+: g') where
  gunify _ (L1 x) (L1 y) = gunify (Proxy @f) x y
  gunify _ (R1 x) (R1 y) = gunify (Proxy @g) x y
  gunify _ _ _ = const Nothing

  gwalk _ k (L1 x) = L1 (gwalk (Proxy @f) k x)
  gwalk _ k (R1 y) = R1 (gwalk (Proxy @g) k y)

  ginject (L1 x) = L1 (ginject x)
  ginject (R1 y) = R1 (ginject y)

  gextract (L1 x) = L1 <$> gextract x
  gextract (R1 y) = R1 <$> gextract y

instance (GLogical f f', GLogical g g') => GLogical (f :*: g) (f' :*: g') where
  gunify _ (x1 :*: y1) (x2 :*: y2) =
    gunify (Proxy @f) x1 x2 >=> gunify (Proxy @g) y1 y2
  gwalk _ k (x :*: y) = gwalk (Proxy @f) k x :*: gwalk (Proxy @g) k y
  ginject (x :*: y) = ginject x :*: ginject y
  gextract (x :*: y) = do
    x' <- gextract x
    y' <- gextract y
    return (x' :*: y')

instance (Logical c) => GLogical (K1 i c) (K1 i' (Term c)) where
  gunify _ (K1 x) (K1 y) = unify' x y
  gwalk _ state (K1 c) = K1 (walk' state c)
  ginject (K1 x) = K1 (inject' x)
  gextract (K1 x) = K1 <$> extract' x

instance (GLogical f f') => GLogical (M1 i t f) (M1 i' t' f') where
  gunify _ (M1 x) (M1 y) = gunify (Proxy @f) x y
  gwalk _ k (M1 m) = M1 (gwalk (Proxy @f) k m)
  ginject (M1 x) = M1 (ginject x)
  gextract (M1 x) = M1 <$> gextract x

genericUnify
  :: forall a
   . (Generic (Logic a), GLogical (Rep a) (Rep (Logic a)))
  => Logic a
  -> Logic a
  -> State
  -> Maybe State
genericUnify l r = gunify (Proxy @(Rep a)) (from l) (from r)

genericWalk
  :: forall a
   . (Generic (Logic a), GLogical (Rep a) (Rep (Logic a)))
  => State
  -> Logic a
  -> Logic a
genericWalk k term = to (gwalk (Proxy @(Rep a)) k (from term))

genericInject
  :: (Generic a, Generic (Logic a), GLogical (Rep a) (Rep (Logic a)))
  => a
  -> Logic a
genericInject x = to (ginject (from x))

-- | The generic implementation of 'extract'.
genericExtract
  :: (Generic a, Generic (Logic a), GLogical (Rep a) (Rep (Logic a)))
  => Logic a
  -> Maybe a
genericExtract x = to <$> gextract (from x)
