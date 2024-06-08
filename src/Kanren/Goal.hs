{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections #-}

-- | Implement and execute relational programs.
module Kanren.Goal (
  -- * The Goal monad
  Goal,
  run,

  -- * Primitive operations
  successo,
  failo,
  (===),
  conj,
  conjMany,
  disj,
  disjMany,
  conde,
  delay,

  -- * Constraints
  (=/=),

  -- * Fresh variables
  Fresh (..),
) where

import Control.Applicative (Alternative (..))
import Control.Monad (ap)
import qualified Data.Foldable as Foldable

import Kanren.Core
import qualified Kanren.Core as Core
import Kanren.Stream

-- $setup
-- >>> :set -package static-minikanren
-- >>> instance Logical Int
-- >>> instance Logical Bool
-- >>> import LogicalBase

-- | A computation in the relational world.
--
-- On its own, a goal performs search in a search tree. It takes some state and
-- transforms it to a stream of new states. But it is better to think of a goal
-- as a relational program. If you want to write a predicate, it will take
-- 'Term's as parameters and return a 'Goal'.
--
-- > zeroo :: Term Int -> Goal ()
-- > zeroo x = x === Value 0
--
-- A 'Goal' is a 'Monad', so you can use the do-notation to write relations.
--
-- > oppositeso :: Term Bool -> Term Bool -> Goal ()
-- > oppositeso x y = do
-- >   x === Value True
-- >   y === Value False
--
-- Sequencing two goals performs 'conj'unction. To make a branch, use
-- 'disj'unction.
--
-- > noto :: Term Bool -> Term Bool -> Goal ()
-- > noto x y = xIsTrue `disj` xIsFalse
-- >  where
-- >   xIsTrue = (x === Value True) `conj` (y === Value False)
-- >   xIsFalse = (x === Value False) `conj` (y === Value True)
--
-- To execute a goal and find its solutions, use 'run'.
--
-- >>> run (\x -> noto (Value False) x)
-- [Value True]
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

-- | Query for solutions of a goal.
--
-- >>> run (\x -> x === Value (42 :: Int))
-- [Value 42]
--
-- You can ask to solve for several variables, or none at all. You can still
-- create intermediate variables inside using 'fresh', but they will not be
-- returned as solutions.
--
-- >>> run (\() -> fresh >>= (\x -> x === Value True))
-- [()]
--
-- Note that there may be several solutions, including infinitely many or zero.
-- If you want to limit the number of solutions, just put it through 'take'.
--
-- >>> take 5 $ run (\x -> disjMany (map (\a -> x === Value a) [0 :: Int ..]))
-- [Value 0,Value 1,Value 2,Value 3,Value 4]
--
-- This function will return logical representation of solutions. This matters
-- for complex types which have a separate logical representation. If you want
-- to transform them back to regular representation, use 'fmap' and 'extract''.
--
-- >>> extract' <$> run (\x -> x === inject' [True])
-- [Just [True]]
--
-- Note that the retrived solutions might be subject to constraints, but it is
-- not yet possible to retrieve them.
run :: (Fresh v) => (v -> Goal ()) -> [v]
run f = Foldable.toList solutions
 where
  states = flip runGoal Core.empty $ do
    vars <- fresh
    f vars
    pure vars
  solutions = fmap (uncurry resolve) states

-- | A goal that always succeeds.
--
-- >>> run (\() -> successo ())
-- [()]
successo :: x -> Goal x
successo = pure

-- | A goal that always fails.
--
-- >>> run (\() -> failo)
-- []
failo :: Goal x
failo = Goal (const Done)

-- | Unify two terms.
--
-- >>> run (\() -> Value 42 === Value (42 :: Int))
-- [()]
-- >>> run (\() -> Value 42 === Value (37 :: Int))
-- []
(===) :: (Logical a) => Term a -> Term a -> Goal ()
a === b = Goal (maybeToStream . fmap (,()) . unify' a b)

-- | Put a constraint that two terms must not be equal.
--
-- >>> run (\x -> (x =/= Value 42) `conj` (x === Value (37 :: Int)))
-- [Value 37]
-- >>> run (\x -> (x =/= Value 42) `conj` (x === Value (42 :: Int)))
-- []
--
-- It is not yet possible to retrieve solutions along with remaining constraints.
(=/=) :: (Logical a) => Term a -> Term a -> Goal ()
a =/= b = Goal (maybeToStream . fmap (,()) . disequality a b)

-- | Perform conjnction of two goals. If the first goal succeeds, run the second
-- goal on its results.
--
-- >>> run (\x -> (x === Value 42) `conj` (x === Value (42 :: Int)))
-- [Value 42]
-- >>> run (\x -> (x === Value 42) `conj` (x === Value (37 :: Int)))
-- []
-- >>> run (\(x, y) -> (x === Value (42 :: Int)) `conj` (y === Value True))
-- [(Value 42,Value True)]
--
-- Note that the do-notation performs conjunction as well, so you will rarely
-- need to use this function directly.
--
-- >>> :{
--   run (\(x, y) -> do
--     x === Value (42 :: Int)
--     y === Value True
--   )
-- :}
-- [(Value 42,Value True)]
conj :: Goal x -> Goal y -> Goal y
conj = (>>)

-- | Perform conjunction of several goals, left to right.
--
-- >>> run (\(x, y) -> conjMany [x === Value (42 :: Int), y === Value True])
-- [(Value 42,Value True)]
conjMany :: [Goal ()] -> Goal ()
conjMany = foldr conj (pure ())

-- | Perform disjunction of two goals. Run the first goal, then the second, and
-- combine their results.
--
-- >>> run (\x -> (x === Value 42) `disj` (x === Value (37 :: Int)))
-- [Value 42,Value 37]
-- >>> run (\x -> (x === Value 42) `disj` (x === Value (42 :: Int)))
-- [Value 42,Value 42]
-- >>> run (\(x, y) -> (x === Value (42 :: Int)) `disj` (y === Value True))
-- [(Value 42,Var (VarId 1)),(Var (VarId 0),Value True)]
disj :: Goal x -> Goal x -> Goal x
disj = (<|>)

-- | Perform disjunction of several goals, left to right.
--
-- >>> run (\x -> disjMany (map (\a -> x === Value a) [1, 3 .. 11 :: Int]))
-- [Value 1,Value 3,Value 5,Value 7,Value 9,Value 11]
disjMany :: [Goal x] -> Goal x
disjMany = delay . foldr disj failo

-- | Consider several possible cases, using syntax similar to @conde@ from
-- @faster-minikanren@.
--
-- >>> :{
--   run (\(x, y) -> conde
--     [ [ x === Value False, y === Value 0 ]
--     , [ x === Value True, y === Value 1 ]
--     ])
-- :}
-- [(Value False,Value 0),(Value True,Value 1)]
--
-- However, this might not be the best syntax for Haskell. Using 'disjMany' with
-- the do-notation may be easier to type and less noisy:
--
-- >>> :{
--   run (\(x, y) -> disjMany
--     [ do
--         x === Value False
--         y === Value 0
--     , do
--         x === Value True
--         y === Value 1
--     ])
-- :}
-- [(Value False,Value 0),(Value True,Value 1)]
--
-- In addition, the "Match" module provides pattern matching over variants,
-- which might better express your intent.
--
-- >>> :{
--   run (\(x, y) -> x & (matche
--     & on _False (\() -> y === Value 0)
--     & on _True (\() -> y === Value 1)))
-- :}
-- [(Value False,Value 0),(Value True,Value 1)]
conde :: [[Goal ()]] -> Goal ()
conde = disjMany . map conjMany

-- | The existential quantifier.
--
-- Whenever you need an intermediate variable, 'fresh' will give you one.
--
-- >>> :{
--   run (\() -> do
--     x <- fresh
--     x === Value (42 :: Int))
-- :}
-- [()]
--
-- Creating a lot of variables one-by-one might be tiresome though. This is why
-- 'fresh' is not a standalone function but a method on a type class. 'Fresh'
-- is implemented not only for @'Term' a@ but for tuples too, so you can ask for
-- several fresh variables at once.
--
-- >>> :{
--   run (\() -> do
--     (x, y) <- fresh
--     x === Value True
--     y === Value False)
-- :}
-- [()]
--
-- In fact, 'run' also uses 'Fresh', so you can choose how many variables you
-- want to solve for.
--
-- >>> :{
--   run (\(x, y) -> do
--     x === Value True
--     y === Value False)
-- :}
-- [(Value True,Value False)]
--
-- As an edge case, you can ask for no variables at all using @()@. While this
-- is not useful inside relations, this is how the first two examples actually
-- work. 'Fresh' is also used for pattern matching from the @"Match"@ module
-- when the matched value is not known yet.
class Fresh v where
  -- | Create fresh variables.
  fresh :: Goal v

  -- | Resolve each variable to its value in the given state. You won't need to
  -- use this method yourself, but 'run' uses it to return solutions.
  resolve :: State -> v -> v

instance Fresh () where
  fresh = delay (pure ())
  resolve _ () = ()

-- | 'makeVariable' in the form of 'Goal'. Does not insert an 'Await' point,
-- while 'fresh' inserts a single point before creating all its variables.
fresh' :: Goal (Term a)
fresh' = Goal (pure . makeVariable)

instance (Logical a) => Fresh (Term a) where
  fresh = delay fresh'
  resolve = walk'

instance (Logical a, Fresh v) => Fresh (Term a, v) where
  fresh = do
    v <- fresh
    a <- fresh'
    pure (a, v)
  resolve state (a, v) = (a', v')
   where
    a' = resolve state a
    v' = resolve state v

instance (Logical a, Logical b, Fresh v) => Fresh (Term a, Term b, v) where
  fresh = do
    (b, v) <- fresh
    a <- fresh'
    pure (a, b, v)
  resolve state (a, b, v) = (a', b', v')
   where
    a' = resolve state a
    (b', v') = resolve state (b, v)

instance
  (Logical a, Logical b, Logical c, Fresh v)
  => Fresh (Term a, Term b, Term c, v)
  where
  fresh = do
    (b, c, v) <- fresh
    a <- fresh'
    pure (a, b, c, v)
  resolve state (a, b, c, v) = (a', b', c', v')
   where
    a' = resolve state a
    (b', c', v') = resolve state (b, c, v)

instance
  (Logical a, Logical b, Logical c, Logical d, Fresh v)
  => Fresh (Term a, Term b, Term c, Term d, v)
  where
  fresh = do
    (b, c, d, v) <- fresh
    a <- fresh'
    pure (a, b, c, d, v)
  resolve state (a, b, c, d, v) = (a', b', c', d', v')
   where
    a' = resolve state a
    (b', c', d', v') = resolve state (b, c, d, v)

instance
  (Logical a, Logical b, Logical c, Logical d, Logical e, Fresh v)
  => Fresh (Term a, Term b, Term c, Term d, Term e, v)
  where
  fresh = do
    (b, c, d, e, v) <- fresh
    a <- fresh'
    pure (a, b, c, d, e, v)
  resolve state (a, b, c, d, e, v) = (a', b', c', d', e', v')
   where
    a' = resolve state a
    (b', c', d', e', v') = resolve state (b, c, d, e, v)

delay :: Goal a -> Goal a
delay (Goal g) = Goal (Await . g)
