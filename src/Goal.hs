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

import Core
import Stream

newtype Goal x = Goal {runGoal :: State -> Stream (State, x)}

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
  empty = failo
  Goal g1 <|> Goal g2 =
    Goal (\state -> g1 state `interleave` g2 state)

failo :: Goal x
failo = Goal (const Done)

(===) :: (Logical a) => Term a -> Term a -> Goal ()
a === b = Goal (maybeToStream . fmap (,()) . unify' a b)

conj :: Goal x -> Goal y -> Goal y
conj = (>>)

conjMany :: [Goal ()] -> Goal ()
conjMany = foldr conj (pure ())

disj :: Goal x -> Goal x -> Goal x
disj = (<|>)

disjMany :: [Goal x] -> Goal x
disjMany = foldr disj failo

conde :: [[Goal ()]] -> Goal ()
conde = disjMany . map conjMany

-- >>> extract' <$> run @[Int] (\ xs -> [1, 2] === Value (LCons 1 xs))
-- [Just [2]]
run :: (Logical a) => (Term a -> Goal ()) -> [Term a]
run f = Foldable.toList solutions
 where
  (initialState, queryVar) = makeVariable Core.empty
  states = fst <$> runGoal (f queryVar) initialState
  solutions = fmap (resolve queryVar) states

class Fresh v where
  fresh :: (v -> Goal x) -> Goal x

instance Fresh () where
  fresh f = f ()

instance Fresh (Term a) where
  fresh f = Goal $ \state ->
    let (state', variable) = makeVariable state
     in runGoal (f variable) state'

instance Fresh (Term a, Term b) where
  fresh f =
    fresh $ \a ->
      fresh $ \b ->
        f (a, b)

instance Fresh (Term a, Term b, Term c) where
  fresh f =
    fresh $ \(a, b) ->
      fresh $ \c ->
        f (a, b, c)
