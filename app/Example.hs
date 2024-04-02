{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE ConstraintKinds #-}

module Example where

import Control.Applicative (Alternative (..))
import GHC.Generics (Generic)

import Core
import DeriveLogic
import GenericUnifiable
import Goal
import UnifiableBase

data TwoInts = Int :* Int
  deriving (Show, Generic)
deriveLogic ''TwoInts

data Record = Record { foo :: Int, bar :: TwoInts }
  deriving (Show, Generic)
deriveLogic ''Record

-- data Erase = forall a. Erase a
-- deriveLogic ''Erase

data Gadt where
  Gadt :: Int -> Gadt
  deriving (Generic)
deriveLogic ''Gadt

data RecordGadt where
  RecordGadt :: { gadt :: Gadt } -> RecordGadt
  deriving (Generic)
deriveLogic ''RecordGadt

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
