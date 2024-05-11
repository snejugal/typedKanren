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
  Logical (..),
  VarId,
  Term (..),
  unify',
  walk',
  inject',
  extract',
  State,
  empty,
  makeVariable,
) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Exts (IsList (..))
import Unsafe.Coerce (unsafeCoerce)

class Logical a where
  type Logic a = r | r -> a
  type Logic a = a

  unify :: Logic a -> Logic a -> State -> Maybe State
  default unify :: (Eq (Logic a)) => Logic a -> Logic a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  walk :: State -> Logic a -> Logic a
  default walk :: (a ~ Logic a) => State -> Logic a -> Logic a
  walk _ = id

  inject :: a -> Logic a
  default inject :: (a ~ Logic a) => a -> Logic a
  inject = id

  extract :: Logic a -> Maybe a
  default extract :: (a ~ Logic a) => Logic a -> Maybe a
  extract = Just

newtype VarId a = VarId Int
  deriving (Show, Eq)

data Term a
  = Var (VarId a)
  | Value (Logic a)

deriving instance (Show (Logic a)) => Show (Term a)
deriving instance (Eq (Logic a)) => Eq (Term a)

instance (IsList (Logic a)) => IsList (Term a) where
  type Item (Term a) = Item (Logic a)
  fromList = Value . fromList

instance (Num (Logic a)) => Num (Term a) where
  fromInteger = Value . fromInteger

unify' :: (Logical a) => Term a -> Term a -> State -> Maybe State
unify' l r state =
  case (shallowWalk state l, shallowWalk state r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst x r' state)
    (l', Var y) -> Just (addSubst y l' state)
    (Value l', Value r') -> unify l' r' state

walk' :: (Logical a) => State -> Term a -> Term a
walk' state x = case shallowWalk state x of
  Var i -> Var i
  Value v -> Value (walk state v)

inject' :: (Logical a) => a -> Term a
inject' = Value . inject

extract' :: (Logical a) => Term a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

data ErasedTerm where
  ErasedTerm :: (Logical a) => Term a -> ErasedTerm

unsafeReconstructTerm :: ErasedTerm -> Term a
unsafeReconstructTerm (ErasedTerm x) = unsafeCoerce x

newtype Subst = Subst (IntMap ErasedTerm)

data State = State
  { knownSubst :: !Subst
  , maxVarId :: !Int
  }

empty :: State
empty = State{knownSubst = Subst IntMap.empty, maxVarId = 0}

makeVariable :: State -> (State, Term a)
makeVariable State{maxVarId, ..} = (state', var)
 where
  var = Var (VarId maxVarId)
  state' = State{maxVarId = maxVarId + 1, ..}

shallowWalk :: (Logical a) => State -> Term a -> Term a
shallowWalk _ (Value v) = Value v
shallowWalk state@State{knownSubst = Subst m} (Var (VarId i)) =
  case IntMap.lookup i m of
    Nothing -> Var (VarId i)
    Just v -> shallowWalk state (unsafeReconstructTerm v)

addSubst :: (Logical a) => VarId a -> Term a -> State -> State
addSubst (VarId i) value State{knownSubst = Subst m, ..} =
  State
    { knownSubst = Subst $ IntMap.insert i (ErasedTerm value) m
    , ..
    }
