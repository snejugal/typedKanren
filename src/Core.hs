{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Core (
  VarId (..), -- TODO: constructor shouldn't be public
  ValueOrVar (..),
  subst',
  unify',
  inject',
  extract',
  apply,
  makeVariable,
  State (..),
  Subst (..),
  Unifiable (..),
) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import GHC.Exts (IsList (..))
import Unsafe.Coerce (unsafeCoerce)

newtype VarId a = VarId Int
  deriving (Show, Eq)

data ValueOrVar a
  = Var (VarId a)
  | Value (Term a)

deriving instance (Show (Term a)) => Show (ValueOrVar a)
deriving instance (Eq (Term a)) => Eq (ValueOrVar a)

instance (IsList (Term a)) => IsList (ValueOrVar a) where
  type Item (ValueOrVar a) = Item (Term a)
  fromList = Value . fromList

instance (Num (Term a)) => Num (ValueOrVar a) where
  fromInteger = Value . fromInteger

subst' :: (Unifiable a) => (forall x. VarId x -> Maybe (ValueOrVar x)) -> ValueOrVar a -> ValueOrVar a
subst' k (Value x) = Value (subst k x)
subst' k x@(Var i) = fromMaybe x (k i)

apply :: (Unifiable a) => Subst -> ValueOrVar a -> ValueOrVar a
apply (Subst m) = subst' (\(VarId i) -> unsafeExtractSomeValue <$> IntMap.lookup i m)

addSubst :: (Unifiable a) => (VarId a, ValueOrVar a) -> State -> State
addSubst (VarId i, value) State{knownSubst = Subst m, ..} =
  State
    { knownSubst =
        Subst $
          IntMap.insert i (SomeValue value) $
            updateSomeValue <$> m
    , ..
    }
 where
  updateSomeValue (SomeValue x) =
    SomeValue (apply (Subst (IntMap.singleton i (SomeValue value))) x)

-- >>> unify' (Value (Pair (Var 0, )))
unify' :: (Unifiable a) => ValueOrVar a -> ValueOrVar a -> State -> Maybe State
unify' l r state@State{..} =
  case (apply knownSubst l, apply knownSubst r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst (x, r') state)
    (l', Var y) -> Just (addSubst (y, l') state)
    (Value l', Value r') -> unify l' r' state

inject' :: (Unifiable a) => a -> ValueOrVar a
inject' = Value . inject

extract' :: (Unifiable a) => ValueOrVar a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

data SomeValue where
  SomeValue :: (Unifiable a) => ValueOrVar a -> SomeValue

unsafeExtractSomeValue :: SomeValue -> ValueOrVar a
unsafeExtractSomeValue (SomeValue x) = unsafeCoerce x

newtype Subst = Subst (IntMap SomeValue)

data State = State
  { knownSubst :: !Subst
  , maxVarId :: !Int
  }

makeVariable :: State -> (State, ValueOrVar a)
makeVariable State{maxVarId, ..} = (State{maxVarId = maxVarId + 1, ..}, Var (VarId maxVarId))

class Unifiable a where
  type Term (a :: Type) = r | r -> a
  type Term a = a

  subst :: (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term a -> Term a
  default subst :: (a ~ Term a) => (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term a -> Term a
  subst _ = id

  unify :: Term a -> Term a -> State -> Maybe State
  default unify :: (Eq (Term a)) => Term a -> Term a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  inject :: a -> Term a
  default inject :: (a ~ Term a) => a -> Term a
  inject = id

  extract :: Term a -> Maybe a
  default extract :: (a ~ Term a) => Term a -> Maybe a
  extract = Just
