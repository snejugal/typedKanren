{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with maybe" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
module Lib where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Exts (Any, IsList(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Control.Monad ((>=>))
import Data.Maybe (maybeToList, fromMaybe)


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

type Goal = State -> [State]

data ValueOrVar a
  = Var (VarId a)
  | Value (Term a)

deriving instance (Show (Term a)) => Show (ValueOrVar a)

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

  subst :: (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term (a, b) -> Term (a, b)
  subst k (x, y) = (subst' k x, subst' k y)

  unify :: Term (a, b) -> Term (a, b) -> State -> Maybe State
  unify (a1, b1) (a2, b2) =
    unify' a1 a2 >=> unify' b1 b2

  inject :: (a, b) -> Term (a, b)
  inject (x, y) = (Value (inject x), Value (inject y))

  extract :: Term (a, b) -> Maybe (a, b)
  extract (Value x, Value y) = do
    x' <- extract x
    y' <- extract y
    return (x', y')
  extract _ = Nothing

data LogicList a
  = LNil
  | LCons (ValueOrVar a) (ValueOrVar [a])

deriving instance (Show (Term a)) => Show (LogicList a)

instance Unifiable a => Unifiable [a] where
  type Term [a] = LogicList a

  subst :: (forall x. VarId x -> Maybe (ValueOrVar x)) -> Term [a] -> Term [a]
  subst _ LNil = LNil
  subst k (LCons x xs) = LCons (subst' k x) (subst' k xs)

  unify :: Term [a] -> Term [a] -> State -> Maybe State
  unify LNil LNil = Just
  unify (LCons x xs) (LCons y ys) =
    unify' x y >=> unify' xs ys
  unify _ _ = const Nothing

  inject :: [a] -> Term [a]
  inject [] = LNil
  inject (x:xs) = LCons (Value (inject x)) (Value (inject xs))

  extract :: Term [a] -> Maybe [a]
  extract LNil = Just []
  extract (LCons (Value x) (Value xs)) = do
    x' <- extract x
    xs' <- extract xs
    return (x' : xs')
  extract _ = Nothing

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

(===) :: Unifiable a => ValueOrVar a -> ValueOrVar a -> Goal
a === b = maybeToList . unify' a b

-- >>> extract' <$> run (\ (xs :: ValueOrVar [Int]) -> [1, 2] === Value (LCons 1 xs))
-- [Just [2]]
run :: Unifiable a => (ValueOrVar a -> Goal) -> [ValueOrVar a]
run f =
  [ apply knownSubst queryVar
  | State{..} <- f queryVar initialState
  ]
  where
    initialState = State
      { knownSubst = Subst IntMap.empty
      , maxVarId = 1
      }
    queryVar = Var (VarId 0)

fresh :: (ValueOrVar a -> Goal) -> Goal
fresh f State{..} = f (Var (VarId maxVarId)) newState
  where
    newState = State
      { maxVarId = maxVarId + 1
      , .. }

conj :: Goal -> Goal -> Goal
conj = (>=>)

conjMany :: [Goal] -> Goal
conjMany = foldr conj (\x -> [x])

disj :: Goal -> Goal -> Goal
disj = (<>)

disjMany :: [Goal] -> Goal
disjMany = foldr disj (const [])

conde :: [[Goal]] -> Goal
conde = disjMany . map conjMany

-- matche :: Unifiable a => ValueOrVar a -> [Term a -> Goal) -> Goal
-- matche (Value v) k = k v
-- matche (Var x) k =

-- >>> extract' <$> run (\ (xs :: ValueOrVar [Int]) -> fresh (\ ys -> appendo xs ys [1, 2, 3]))
-- [Just [],Just [1],Just [1,2],Just [1,2,3]]
appendo :: Unifiable a => ValueOrVar [a] -> ValueOrVar [a] -> ValueOrVar [a] -> Goal
appendo xs ys zs =
  conde
    [ [ [] === xs
      , ys === zs ]
    , [ fresh $ \ x ->
          fresh $ \ xs' ->
            conjMany
            [ Value (LCons x xs') === xs
            , fresh $ \ z ->
                fresh $ \ zs' ->
                  conjMany
                  [ Value (LCons z zs') === zs
                  , x === z
                  , appendo xs' ys zs'
                  ]
            ]]]


-- -- safer, but not really, and not efficient
-- data Subst' where
-- 	NoSubst :: Subst'
-- 	SomeSubst :: (VarId a, a) -> Subst' -> Subst'


-- newtype Variable a = Variable Int deriving (Show, Eq)

-- data Value a = Unknown (Variable a) | Known a deriving (Show)

-- data State a = State [(Variable a, Value a)] (Variable a)

-- class Term a where
-- 	unify :: a -> a -> State a -> Maybe (State a)

-- unifyEq :: Eq a => a -> a -> State a -> Maybe (State a)
-- unifyEq x y state
-- 	| x == y = Just state
-- 	| otherwise = Nothing

-- instance Term Bool where
-- 	unify = unifyEq

-- instance Term Int where
-- 	unify = unifyEq

-- instance Term Integer where
-- 	unify = unifyEq

-- -- data LogicList a = Nil | Cons (Value a) (Value (LogicList a)) deriving (Show)
-- --
-- -- instance Term a => Term (LogicList a) where
-- --     unify Nil Nil state = Just state
-- --     unify (Cons x xs) (Cons y ys) state = unify x y state >>= unify xs ys

-- apply :: Value a -> State a -> Value a
-- apply value@(Known _) _ = value
-- apply (Unknown variable) (State values _) = case lookup variable values of
-- 	Just value -> value
-- 	Nothing -> Unknown variable

-- unify' :: Term a => Value a -> Value a -> State a -> Maybe (State a)
-- unify' left right state = case (left', right') of
-- 	(Unknown left'', Unknown right'') | left'' == right'' -> Just state
-- 	(Unknown variable, value) -> insert variable value
-- 	(value, Unknown variable) -> insert variable value
-- 	(Known left'', Known right'') -> unify left'' right'' state
--   where
-- 	left' = apply left state
-- 	right' = apply right state

-- 	State values nextVariable = state
-- 	insert variable value =
-- 		Just (State ((variable, value) : values) nextVariable)

-- type Goal a = State a -> [State a]

-- (===) :: Term a => Value a -> Value a -> Goal a
-- a === b = maybeToList . unify' a b

-- run :: (Value a -> Goal a) -> [Value a]
-- run f = map (apply initialVariable) (goal state)
--   where
-- 	state = State [] (Variable 1)
-- 	initialVariable = Unknown (Variable 0)
-- 	goal = f initialVariable
