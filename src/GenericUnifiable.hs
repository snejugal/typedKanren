{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module GenericUnifiable (
  GUnifiable,
  genericSubst,
  genericUnify,
  genericInject,
  genericExtract,
  genericFresh
) where

import Control.Monad ((>=>))
import GHC.Generics
import Data.Proxy (Proxy(..))

import Core
import Goal

class GUnifiable f f' where
  gsubst :: Proxy f -> (forall x. VarId x -> Maybe (ValueOrVar x)) -> f' p -> f' p
  gunify :: Proxy f -> f' p -> f' p -> State -> Maybe State
  ginject :: f p -> f' p
  gextract :: f' p -> Maybe (f p)
  gfresh :: Proxy f -> (f' p -> Goal ()) -> Goal ()

instance GUnifiable V1 V1 where
  gsubst _ _ = id
  gunify _ _ _ = Just
  ginject = id
  gextract = Just
  gfresh _ _ = return ()

instance GUnifiable U1 U1 where
  gsubst _ _ = id
  gunify _ _ _ = Just
  ginject = id
  gextract = Just
  gfresh _ k = k U1

instance (GUnifiable f f', GUnifiable g g') => GUnifiable (f :+: g) (f' :+: g') where
  gsubst _ k (L1 x) = L1 (gsubst (Proxy @f) k x)
  gsubst _ k (R1 y) = R1 (gsubst (Proxy @g) k y)

  gunify _ (L1 x) (L1 y) = gunify (Proxy @f) x y
  gunify _ (R1 x) (R1 y) = gunify (Proxy @g) x y
  gunify _ _ _ = const Nothing

  ginject (L1 x) = L1 (ginject x)
  ginject (R1 y) = R1 (ginject y)

  gextract (L1 x) = L1 <$> gextract x
  gextract (R1 y) = R1 <$> gextract y

  gfresh _ k = disj
    (gfresh (Proxy @f) (k . L1))
    (gfresh (Proxy @g) (k . R1))

instance (GUnifiable f f', GUnifiable g g') => GUnifiable (f :*: g) (f' :*: g') where
  gsubst _ k (x :*: y) = gsubst (Proxy @f) k x :*: gsubst (Proxy @g) k y
  gunify _ (x1 :*: y1) (x2 :*: y2) =
    gunify (Proxy @f) x1 x2 >=> gunify (Proxy @g) y1 y2
  ginject (x :*: y) = ginject x :*: ginject y
  gextract (x :*: y) = do
    x' <- gextract x
    y' <- gextract y
    return (x' :*: y')
  gfresh _ k =
    gfresh (Proxy @f) $ \x ->
      gfresh (Proxy @g) $ \y ->
        k (x :*: y)

instance Unifiable c => GUnifiable (K1 i c) (K1 i' (ValueOrVar c)) where
  gsubst _ k (K1 c) = K1 (subst' k c)
  gunify _ (K1 x) (K1 y) = unify' x y
  ginject (K1 x) = K1 (inject' x)
  gextract (K1 x) = K1 <$> extract' x
  gfresh _ k = fresh' (k . K1)

instance GUnifiable f f' => GUnifiable (M1 i t f) (M1 i' t' f') where
  gsubst _ k (M1 m) = M1 (gsubst (Proxy @f) k m)
  gunify _ (M1 x) (M1 y) = gunify (Proxy @f) x y
  ginject (M1 x) = M1 (ginject x)
  gextract (M1 x) = M1 <$> gextract x
  gfresh _ k = gfresh (Proxy @f) (k . M1)

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  type Term (a, b) = (ValueOrVar a, ValueOrVar b)
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

genericSubst
  :: forall a. (Generic (Term a), GUnifiable (Rep a) (Rep (Term a)))
  => (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term a -> Term a
genericSubst k term = to (gsubst (Proxy @(Rep a)) k (from term))

genericUnify
  :: forall a. (Generic (Term a), GUnifiable (Rep a) (Rep (Term a)))
  => Term a -> Term a -> State -> Maybe State
genericUnify l r = gunify (Proxy @(Rep a)) (from l) (from r)

genericInject
  :: (Generic a, Generic (Term a), GUnifiable (Rep a) (Rep (Term a)))
  => a -> Term a
genericInject x = to (ginject (from x))

genericExtract
  :: (Generic a, Generic (Term a), GUnifiable (Rep a) (Rep (Term a)))
  => Term a -> Maybe a
genericExtract x = to <$> gextract (from x)

genericFresh
  :: forall a. (Generic (Term a), GUnifiable (Rep a) (Rep (Term a)))
  => (Term a -> Goal ()) -> Goal ()
genericFresh k = gfresh (Proxy @(Rep a)) (k . to)
