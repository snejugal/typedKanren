{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
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
  Logical (..),
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
  | Value (Logic a)

deriving instance (Show (Logic a)) => Show (ValueOrVar a)
deriving instance (Eq (Logic a)) => Eq (ValueOrVar a)

instance (IsList (Logic a)) => IsList (ValueOrVar a) where
  type Item (ValueOrVar a) = Item (Logic a)
  fromList = Value . fromList

instance (Num (Logic a)) => Num (ValueOrVar a) where
  fromInteger = Value . fromInteger

subst' :: (Logical a) => (forall x. VarId x -> Maybe (ValueOrVar x)) -> ValueOrVar a -> ValueOrVar a
subst' k (Value x) = Value (subst k x)
subst' k x@(Var i) = fromMaybe x (k i)

apply :: (Logical a) => Subst -> ValueOrVar a -> ValueOrVar a
apply (Subst m) = subst' (\(VarId i) -> unsafeExtractSomeValue <$> IntMap.lookup i m)

addSubst :: (Logical a) => (VarId a, ValueOrVar a) -> State -> State
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
unify' :: (Logical a) => ValueOrVar a -> ValueOrVar a -> State -> Maybe State
unify' l r state@State{..} =
  case (apply knownSubst l, apply knownSubst r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst (x, r') state)
    (l', Var y) -> Just (addSubst (y, l') state)
    (Value l', Value r') -> unify l' r' state

inject' :: (Logical a) => a -> ValueOrVar a
inject' = Value . inject

extract' :: (Logical a) => ValueOrVar a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

data SomeValue where
  SomeValue :: (Logical a) => ValueOrVar a -> SomeValue

unsafeExtractSomeValue :: SomeValue -> ValueOrVar a
unsafeExtractSomeValue (SomeValue x) = unsafeCoerce x

newtype Subst = Subst (IntMap SomeValue)

data State = State
  { knownSubst :: !Subst
  , maxVarId :: !Int
  }

makeVariable :: State -> (State, ValueOrVar a)
makeVariable State{maxVarId, ..} = (State{maxVarId = maxVarId + 1, ..}, Var (VarId maxVarId))

class Logical a where
  type Logic (a :: Type) = r | r -> a
  type Logic a = a

  subst :: (forall x. VarId x -> Maybe (ValueOrVar x)) -> Logic a -> Logic a
  default subst :: (a ~ Logic a) => (forall x. VarId x -> Maybe (ValueOrVar x)) -> Logic a -> Logic a
  subst _ = id

  unify :: Logic a -> Logic a -> State -> Maybe State
  default unify :: (Eq (Logic a)) => Logic a -> Logic a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  inject :: a -> Logic a
  default inject :: (a ~ Logic a) => a -> Logic a
  inject = id

  extract :: Logic a -> Maybe a
  default extract :: (a ~ Logic a) => Logic a -> Maybe a
  extract = Just
