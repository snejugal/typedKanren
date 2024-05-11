{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module GenericLogical (
  GLogical,
  genericUnify,
  genericWalk,
  genericInject,
  genericExtract,
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

genericExtract
  :: (Generic a, Generic (Logic a), GLogical (Rep a) (Rep (Logic a)))
  => Logic a
  -> Maybe a
genericExtract x = to <$> gextract (from x)
