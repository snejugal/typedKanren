{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with maybe" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Exts (IsList(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Control.Monad ((>=>))
import Data.Maybe (fromMaybe)
import Control.Applicative (Alternative (..))
import GHC.Generics
import Data.Proxy (Proxy(..))
import qualified Data.Foldable as Foldable

import Stream

-- TODO:
-- 1. Split into modules
-- 2. Generate Logic data types fully automatically (probably via Template Haskell)
-- 3. Document everything
-- 4. Add tests
-- 5. Implement fair disjunction
-- 6. Think about nested patterns for matche
-- 7. Add symbolic constraints (e.g. disequality, relations for numbers)
-- 8. Maybe, allow effects (a la LogicT)
-- 9. Benchmark
-- 10. Add more examples

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

-- data Id a = Id a

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

-- Variable Identifiers -- machine-sized integers!
-- Terms?
-- Substitutions -- map from variable identifier to a term
-- State
-- Goal

newtype VarId a = VarId Int
  deriving (Show, Eq)

data SomeValue where
  SomeValue :: Unifiable a => ValueOrVar a -> SomeValue

newtype Subst = Subst (IntMap SomeValue)

data State = State
  { knownSubst :: !Subst
  , maxVarId   :: !Int
  }

newtype Goal (a :: Type) = Goal { runGoal :: State -> Stream State }

instance Functor Goal where
  fmap _ (Goal g) = Goal g

instance Applicative Goal where
  pure _ = Goal pure
  Goal g1 <*> Goal g2 = Goal (g1 >=> g2)

instance Monad Goal where
  return = pure
  (>>) = (*>)
  Goal g1 >>= f = Goal (g1 >=> g2)
    where
      Goal g2 = f (error "Goal is not a Monad!")

instance Alternative Goal where
  empty = Goal (const Done)
  Goal g1 <|> Goal g2 =
    Goal (\state -> g1 state `interleave` g2 state)

data ValueOrVar a
  = Var (VarId a)
  | Value (Term a)

deriving instance (Show (Term a)) => Show (ValueOrVar a)
deriving instance (Eq (Term a)) => Eq (ValueOrVar a)

class Unifiable a where
  type Term (a :: Type) = r | r -> a
  type Term a = a

  subst :: (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term a -> Term a
  default subst :: (a ~ Term a) => (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term a -> Term a
  subst _ = id

  unify :: Term a -> Term a -> State -> Maybe State
  default unify :: Eq (Term a) => Term a -> Term a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  inject :: a -> Term a
  default inject :: (a ~ Term a) => a -> Term a
  inject = id

  extract :: Term a -> Maybe a
  default extract :: (a ~ Term a) => Term a -> Maybe a
  extract = Just

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  type Term (a, b) = (ValueOrVar a, ValueOrVar b)
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

data LogicList a
  = LNil
  | LCons (ValueOrVar a) (ValueOrVar [a])
  deriving (Generic)

deriving instance (Show (Term a)) => Show (LogicList a)

instance Unifiable a => Unifiable [a] where
  type Term [a] = LogicList a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList a) where
  type Item (LogicList a) = ValueOrVar a
  fromList [] = LNil
  fromList (x:xs) = LCons x (Value (fromList xs))

instance IsList (Term a) => IsList (ValueOrVar a) where
  type Item (ValueOrVar a) = Item (Term a)
  fromList = Value . fromList

instance Num (Term a) => Num (ValueOrVar a) where
  fromInteger = Value . fromInteger

instance Unifiable Int
instance Unifiable Bool
instance Eq (Term a) => Unifiable (ValueOrVar a)  -- ???

addSubst :: Unifiable a => (VarId a, ValueOrVar a) -> State -> State
addSubst (VarId i, value) State{knownSubst = Subst m, ..} = State
  { knownSubst = Subst $
      IntMap.insert i (SomeValue value) $
        updateSomeValue <$> m
  , .. }
  where
    updateSomeValue (SomeValue x) =
      SomeValue (apply (Subst (IntMap.singleton i (SomeValue value))) x)

subst' :: Unifiable a => (forall x. VarId x -> Maybe (ValueOrVar x)) -> ValueOrVar a -> ValueOrVar a
subst' k (Value x) = Value (subst k x)
subst' k x@(Var i) = fromMaybe x (k i)

-- >>> unify' (Value (Pair (Var 0, )))
unify' :: Unifiable a => ValueOrVar a -> ValueOrVar a -> State -> Maybe State
unify' l r state@State{..} =
  case (apply knownSubst l, apply knownSubst r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst (x, r') state)
    (l', Var y) -> Just (addSubst (y, l') state)
    (Value l', Value r') -> unify l' r' state

inject' :: Unifiable a => a -> ValueOrVar a
inject' = Value . inject

extract' :: Unifiable a => ValueOrVar a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

apply :: Unifiable a => Subst -> ValueOrVar a -> ValueOrVar a
apply (Subst m) = subst' (\(VarId i) -> unsafeExtractSomeValue <$> IntMap.lookup i m)

unsafeExtractSomeValue :: SomeValue -> ValueOrVar a
unsafeExtractSomeValue (SomeValue x) = unsafeCoerce x

(===) :: Unifiable a => ValueOrVar a -> ValueOrVar a -> Goal ()
a === b = Goal (maybeToStream . unify' a b)

-- >>> extract' <$> run @[Int] (\ xs -> [1, 2] === Value (LCons 1 xs))
-- [Just [2]]
run :: Unifiable a => (ValueOrVar a -> Goal ()) -> [ValueOrVar a]
run f = Foldable.toList (fmap resolveQueryVar (runGoal (f queryVar) initialState))
  where
    initialState = State
      { knownSubst = Subst IntMap.empty
      , maxVarId = 1
      }
    queryVar = Var (VarId 0)
    resolveQueryVar State{..} = apply knownSubst queryVar

fresh' :: (ValueOrVar a -> Goal b) -> Goal b
fresh' f = Goal $ \State{..} ->
  let newState = State
        { maxVarId = maxVarId + 1
        , .. }
  in runGoal (f (Var (VarId maxVarId))) newState

class Unifiable a => UnifiableFresh a where
  fresh :: (Term a -> Goal ()) -> Goal ()

instance (Unifiable a, Unifiable b) => UnifiableFresh (a, b) where
  fresh = genericFresh

instance (Unifiable a) => UnifiableFresh [a] where
  fresh = genericFresh

conj :: Goal () -> Goal () -> Goal ()
conj g1 g2 = do
  g1
  g2

conjMany :: [Goal ()] -> Goal ()
conjMany = foldr conj (pure ())

disj :: Goal a -> Goal a -> Goal a
disj = (<|>)

disjMany :: [Goal a] -> Goal a
disjMany = foldr disj empty

conde :: [[Goal ()]] -> Goal ()
conde = disjMany . map conjMany

matche :: UnifiableFresh a => ValueOrVar a -> (Term a -> Goal ()) -> Goal ()
matche (Value v) k = k v
matche x@Var{} k =
  fresh $ \v -> do
    x === Value v
    k v

-- >>> extract' <$> run @[Int] (\ xs -> fresh' (\ ys -> appendo xs ys [1, 2, 3]))
-- [Just [],Just [1],Just [1,2],Just [1,2,3]]
appendo :: Unifiable a => ValueOrVar [a] -> ValueOrVar [a] -> ValueOrVar [a] -> Goal ()
appendo xs ys zs =
  matche xs $ \case
    LNil -> ys === zs
    LCons x xs' ->
      matche zs $ \case
        LCons z zs' -> do
          x === z
          appendo xs' ys zs'
        _ -> empty

allo :: Unifiable a => (ValueOrVar a -> Goal ()) -> ValueOrVar [a] -> Goal ()
allo p xs =
  matche xs $ \case
    LNil -> return ()
    LCons y ys -> do
      p y
      allo p ys

data Pair a = Pair a a
  deriving (Eq, Show, Generic)

data LogicPair a = LogicPair (ValueOrVar a) (ValueOrVar a)
  deriving (Generic)

deriving instance (Eq (Term a)) => Eq (LogicPair a)
deriving instance (Show (Term a)) => Show (LogicPair a)

instance Unifiable a => Unifiable (Pair a) where
  type Term (Pair a) = LogicPair a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

matchLogicPair :: Unifiable a => ValueOrVar (Pair a) -> Maybe (Goal (Term (Pair a)))
matchLogicPair (Value t@LogicPair{}) = Just (return t)
matchLogicPair var@Var{} = Just $
  fresh' $ \x ->
    fresh' $ \y -> do
      let t = LogicPair x y
      var === Value t
      return t

pattern LPair' :: Unifiable a => Goal (LogicPair a) -> ValueOrVar (Pair a)
pattern LPair' lpair <- (matchLogicPair -> Just lpair)

both :: Unifiable a => (ValueOrVar a -> Goal ()) -> ValueOrVar (Pair a) -> Goal ()
both p = \case
  LPair' xy -> xy >>= \case
    LogicPair x y -> do
      p x
      p y

matchLNil :: Unifiable a => ValueOrVar [a] -> Maybe (Goal (Term [a]))
matchLNil = \case
  Value t@LNil -> Just (return t)
  var@Var{} -> Just $ do
    let t = LNil
    var === Value t
    return t
  _ -> Nothing

matchLCons :: Unifiable a => ValueOrVar [a] -> Maybe (Goal (Term [a]))
matchLCons = \case
  Value t@LCons{} -> Just (return t)
  var@Var{} -> Just $ do
    fresh' $ \x ->
      fresh' $ \xs -> do
        let t = LCons x xs
        var === Value t
        return t
  _ -> Nothing

pattern LNil' :: Unifiable a => Goal (Term [a]) -> ValueOrVar [a]
pattern LNil' g <- (matchLNil -> Just g)

pattern LCons' :: Unifiable a => Goal (Term [a]) -> ValueOrVar [a]
pattern LCons' g <- (matchLCons -> Just g)

allo' :: Unifiable a => (ValueOrVar a -> Goal ()) -> ValueOrVar [a] -> Goal ()
allo' p = \case
  LNil' g -> g >>= \case
    LNil -> return ()
    _ -> error "impossible"
  LCons' g -> g >>= \case
    LCons y ys -> do
      p y
      allo' p ys
    _ -> error "impossible"
