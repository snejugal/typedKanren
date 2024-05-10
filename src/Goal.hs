{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
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
run :: (Fresh v) => (v -> Goal ()) -> [v]
run f = Foldable.toList solutions
 where
  states = flip runGoal Core.empty $ do
    vars <- fresh
    f vars
    pure vars
  solutions = fmap (uncurry resolve) states

class Fresh v where
  fresh :: Goal v
  resolve :: State -> v -> v

instance Fresh () where
  fresh = pure ()
  resolve _ () = ()

instance (Logical a) => Fresh (Term a) where
  fresh = Goal (pure . makeVariable)
  resolve = walk

instance (Logical a, Logical b) => Fresh (Term a, Term b) where
  fresh = do
    a <- fresh
    b <- fresh
    pure (a, b)
  resolve state (a, b) = (a', b')
   where
    a' = walk state a
    b' = walk state b

instance (Logical a, Logical b, Logical c) => Fresh (Term a, Term b, Term c) where
  fresh = do
    (a, b) <- fresh
    c <- fresh
    pure (a, b, c)
  resolve state (a, b, c) = (a', b', c')
   where
    a' = walk state a
    b' = walk state b
    c' = walk state c
