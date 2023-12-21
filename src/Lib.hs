{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with maybe" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Lib where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Exts (IsList(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Control.Monad ((>=>), ap)
import Data.Maybe (maybeToList, fromMaybe)
import Control.Applicative (Alternative (..))
import GHC.Generics
import Data.Proxy (Proxy(..))

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

class GUnifiable f f' where
  gsubst :: Proxy f -> (forall x. VarId x -> Maybe (ValueOrVar x)) -> f' p -> f' p
  gunify :: Proxy f -> f' p -> f' p -> State -> Maybe State
  ginject :: f p -> f' p
  gextract :: f' p -> Maybe (f p)

instance GUnifiable V1 V1 where
  gsubst _ _ = id
  gunify _ _ _ = Just
  ginject = id
  gextract = Just

instance GUnifiable U1 U1 where
  gsubst _ _ = id
  gunify _ _ _ = Just
  ginject = id
  gextract = Just

data Triple a = Triple a a a

-- Rec0 a :*: (Rec0 a :*: Rec0 a)
-- Rec0 (ValueOrVar a) :*: (Rec0 (ValueOrVar a) :*: Rec0 (ValueOrVar a))

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

instance (GUnifiable f f', GUnifiable g g') => GUnifiable (f :*: g) (f' :*: g') where
  gsubst _ _ = id
  gunify _ _ _ = Just
  ginject (x :*: y) = ginject x :*: ginject y
  gextract (x :*: y) = do
    x' <- gextract x
    y' <- gextract y
    return (x' :*: y')

-- data Id a = Id a

instance Unifiable c => GUnifiable (K1 i c) (K1 i' (ValueOrVar c)) where
  gsubst _ k (K1 c) = K1 (subst' k c)
  gunify _ (K1 x) (K1 y) = unify' x y
  ginject (K1 x) = K1 (inject' x)
  gextract (K1 x) = K1 <$> extract' x

instance GUnifiable f f' => GUnifiable (M1 i t f) (M1 i' t' f') where
  gsubst _ k (M1 m) = M1 (gsubst (Proxy @f) k m)
  gunify _ (M1 x) (M1 y) = gunify (Proxy @f) x y
  ginject (M1 x) = M1 (ginject x)
  gextract (M1 x) = M1 <$> gextract x


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

newtype Goal (a :: Type) = Goal { runGoal :: State -> [State] }

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
  empty = Goal (const [])
  Goal g1 <|> Goal g2 =
    Goal (g1 <> g2)

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

data Tree a
  = Empty
  | Leaf a
  | Node [Tree a]
  deriving (Generic, Show)

data LogicTree a
  = LEmpty
  | LLeaf (ValueOrVar a)
  | LNode (ValueOrVar [Tree a])
  deriving (Generic)
deriving instance (Show (Term a)) => Show (LogicTree a)

instance Unifiable a => Unifiable (Tree a) where
  type Term (Tree a) = LogicTree a
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
instance Eq (Term a) => Unifiable (ValueOrVar a)

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
a === b = Goal (maybeToList . unify' a b)

-- >>> extract' <$> run (\ (xs :: ValueOrVar [Int]) -> [1, 2] === Value (LCons 1 xs))
-- [Just [2]]
run :: Unifiable a => (ValueOrVar a -> Goal ()) -> [ValueOrVar a]
run f =
  [ apply knownSubst queryVar
  | State{..} <- runGoal (f queryVar) initialState
  ]
  where
    initialState = State
      { knownSubst = Subst IntMap.empty
      , maxVarId = 1
      }
    queryVar = Var (VarId 0)

fresh :: (ValueOrVar a -> Goal ()) -> Goal ()
fresh f = Goal $ \State{..} ->
  let newState = State
        { maxVarId = maxVarId + 1
        , .. }
  in runGoal (f (Var (VarId maxVarId))) newState

class Unifiable a => UnifiableTuple a where
  freshTuple :: (Term a -> Goal ()) -> Goal ()

instance (Unifiable a, Unifiable b) => UnifiableTuple (a, b) where
  freshTuple f =
    fresh $ \x ->
      fresh $ \y ->
        f (x, y)

instance (Unifiable a) => UnifiableTuple [a] where
  freshTuple f = disjMany
    [ f LNil
    , fresh $ \x ->
        fresh $ \xs ->
          f (LCons x xs)
    ]

instance Unifiable a => UnifiableTuple (Tree a) where
  freshTuple f = disjMany
    [ f LEmpty
    , fresh $ \x -> f (LLeaf x)
    , fresh $ \subtrees ->
        f (LNode subtrees)
    ]


instance Eq (Term a) => UnifiableTuple (ValueOrVar a) where
  freshTuple = fresh

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

matche :: UnifiableTuple a => ValueOrVar a -> (Term a -> Goal ()) -> Goal ()
matche (Value v) k = k v
matche x@Var{} k =
  freshTuple $ \v ->
    conj (x === Value v) (k v)

-- >>> extract' <$> run (\ (xs :: ValueOrVar [Int]) -> fresh (\ ys -> appendo xs ys [1, 2, 3]))
-- [Just [],Just [1],Just [1,2],Just [1,2,3]]
appendo :: Unifiable a => ValueOrVar [a] -> ValueOrVar [a] -> ValueOrVar [a] -> Goal ()
appendo xs ys zs =
  -- matche (xs, zs) $ \case
  --   ([], _) -> ys === zs
  --   (LCons x xs', LCons z zs') ->
  --     conj (x === z) (appendo xs' ys zs')
  --   _ -> const []
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

-- >>> take 5 (run (tree @Int))
-- [Just Empty,Nothing,Just (Node []),Nothing,Nothing]
tree :: Unifiable a => ValueOrVar (Tree a) -> Goal ()
tree t =
  matche t $ \case
    LEmpty -> return ()
    LLeaf _ -> return ()
    LNode subtrees -> allo tree subtrees
