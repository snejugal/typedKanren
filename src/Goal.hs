{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Goal (
  Goal (..),
  failo,
  (===),
  conj,
  conjMany,
  disj,
  disjMany,
  conde,
  run,
  Fresh (..),
) where

import Control.Applicative (Alternative (..))
import Control.Monad (ap)
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import Data.Kind (Type)

import Core
import Stream

newtype Goal (a :: Type) = Goal {runGoal :: State -> Stream (State, a)}

instance Functor Goal where
  fmap f (Goal g) = Goal (fmap (fmap (fmap f)) g)

instance Applicative Goal where
  pure x = Goal (\s -> Yield (s, x) Done)
  (<*>) = ap

instance Monad Goal where
  return = pure
  (>>) = (*>)
  Goal g1 >>= f = Goal $ \s -> do
    (s', x) <- g1 s
    runGoal (f x) s'

instance Alternative Goal where
  empty = Goal (const Done)
  Goal g1 <|> Goal g2 =
    Goal (\state -> g1 state `interleave` g2 state)

failo :: Goal x
failo = Goal (const Done)

(===) :: (Unifiable a) => ValueOrVar a -> ValueOrVar a -> Goal ()
a === b = Goal (maybeToStream . fmap (,()) . unify' a b)

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

-- >>> extract' <$> run @[Int] (\ xs -> [1, 2] === Value (LCons 1 xs))
-- [Just [2]]
run :: (Unifiable a) => (ValueOrVar a -> Goal ()) -> [ValueOrVar a]
run f = Foldable.toList (fmap (resolveQueryVar . fst) (runGoal (f queryVar) initialState))
 where
  initialState =
    State
      { knownSubst = Subst IntMap.empty
      , maxVarId = 1
      }
  queryVar = Var (VarId 0)
  resolveQueryVar State{..} = apply knownSubst queryVar

class Fresh a where
  fresh :: (a -> Goal x) -> Goal x

instance Fresh () where
  fresh f = f ()

instance Fresh (ValueOrVar a) where
  fresh f = Goal $ \state ->
    let (state', variable) = makeVariable state
     in runGoal (f variable) state'

instance Fresh (ValueOrVar a, ValueOrVar b) where
  fresh f =
    fresh $ \a ->
      fresh $ \b ->
        f (a, b)

instance Fresh (ValueOrVar a, ValueOrVar b, ValueOrVar c) where
  fresh f =
    fresh $ \(a, b) ->
      fresh $ \c ->
        f (a, b, c)
