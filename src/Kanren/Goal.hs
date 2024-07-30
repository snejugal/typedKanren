{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

-- | Implement and execute relational programs.
module Kanren.Goal (
  -- * The Goal monad
  Goal,
  run,
  run',

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
import Control.Monad.ST (ST)

import Kanren.Core
import qualified Kanren.Core as Core
import Kanren.Stream (StreamT (..), interleave, maybeToStream)
import qualified Kanren.Stream as Stream

infix 4 ===, =/=
infixr 3 `conj`
infixr 2 `disj`

-- $setup
-- >>> :set -package typedKanren
-- >>> instance Logical Int
-- >>> instance Logical Bool
-- >>> import Kanren.LogicalBase

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
-- >   xIsTrue = x === Value True `conj` y === Value False
-- >   xIsFalse = x === Value False `conj` y === Value True
--
-- To execute a goal and find its solutions, use 'run'.
--
-- >>> run (\x -> noto (Value False) x)
-- [Value True]
newtype Goal s x = Goal {runGoal :: State s -> StreamT (ST s) (State s, x)}

instance Functor (Goal s) where
  fmap f (Goal g) = Goal (fmap (fmap (fmap f)) g)

instance Applicative (Goal s) where
  pure x = Goal (pure . (,x))
  (<*>) = ap

instance Monad (Goal s) where
  return = pure
  (>>) = (*>)
  Goal g1 >>= f = Goal $ \s -> do
    (s', x) <- g1 s
    runGoal (f x) s'

unsafeDisjunction :: Goal s x -> Goal s x -> Goal s x
unsafeDisjunction (Goal g1) (Goal g2) = Goal (\state -> g1 state `interleave` g2 state)

newGoalScope :: Goal s x -> Goal s x
newGoalScope (Goal g) = Goal $ \state -> M (g <$> newScope state)

delay :: Goal s a -> Goal s a
delay (Goal g) = Goal (Await . pure . g)

instance Alternative (Goal s) where
  empty = failo
  (<|>) = disj

-- | Query for solutions of a goal.
--
-- >>> run (\x -> x === Value (42 :: Int))
-- [42]
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
-- [0,1,2,3,4]
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
run :: (Fresh s v) => Int -> (v -> Goal s ()) -> ST s [v]
run n = run'' (Stream.take n)

run' :: (Fresh s v) => (v -> Goal s ()) -> ST s [v]
run' = run'' id

run'' :: (Fresh s v) => (forall a. StreamT (ST s) a -> StreamT (ST s) a) -> (v -> Goal s ()) -> ST s [v]
run'' cutStream f = do
  initialState <- Core.empty
  let goal = fresh >>= (\vars -> f vars >> pure vars)
  let states = cutStream (runGoal goal initialState)
  Stream.toList (uncurry resolve) states

-- | A goal that always succeeds.
--
-- >>> run (\() -> successo ())
-- [()]
successo :: x -> Goal s x
successo = pure

-- | A goal that always fails.
--
-- >>> run (\() -> failo)
-- []
failo :: Goal s x
failo = Goal (const Done)

-- | Unify two terms.
--
-- >>> run (\() -> Value 42 === Value (42 :: Int))
-- [()]
-- >>> run (\() -> Value 42 === Value (37 :: Int))
-- []
(===) :: (Logical a) => Term s a -> Term s a -> Goal s ()
a === b = Goal $ \state ->
  M (fmap (,()) . maybeToStream <$> unify' a b state)

-- (maybeToStream <$> fmap (,()) . unify' a b)
--   where
--     k = fmap (,()) . unify' a b

-- | Put a constraint that two terms must not be equal.
--
-- >>> run (\x -> x =/= Value 42 `conj` x === Value (37 :: Int))
-- [37]
-- >>> run (\x -> x =/= Value 42 `conj` x === Value (42 :: Int))
-- []
--
-- It is not yet possible to retrieve solutions along with remaining constraints.
(=/=) :: (Logical a) => Term s a -> Term s a -> Goal s ()
a =/= b = Goal $ \state ->
  M (fmap (,()) . maybeToStream <$> disequality a b state)

-- | Perform conjnction of two goals. If the first goal succeeds, run the second
-- goal on its results.
--
-- >>> run (\x -> x === Value 42 `conj` x === Value (42 :: Int))
-- [42]
-- >>> run (\x -> x === Value 42 `conj` x === Value (37 :: Int))
-- []
-- >>> run (\(x, y) -> x === Value (42 :: Int) `conj` y === Value True)
-- [(42,True)]
--
-- Note that the do-notation performs conjunction as well, so you will rarely
-- need to use this function directly.
--
-- >>> :{
--  run (\(x, y) -> do
--    x === Value (42 :: Int)
--    y === Value True
--  )
-- :}
-- [(42,True)]
conj :: Goal s x -> Goal s y -> Goal s y
conj = (>>)

-- | Perform conjunction of several goals, left to right.
--
-- >>> run (\(x, y) -> conjMany [x === Value (42 :: Int), y === Value True])
-- [(42,True)]
conjMany :: [Goal s ()] -> Goal s ()
conjMany = foldr conj (pure ())

-- | Perform disjunction of two goals. Run the first goal, then the second, and
-- combine their results.
--
-- >>> run (\x -> x === Value 42 `disj` x === Value (37 :: Int))
-- [42,37]
-- >>> run (\x -> x === Value 42 `disj` x === Value (42 :: Int))
-- [42,42]
-- >>> run (\(x, y) -> x === Value (42 :: Int) `disj` y === Value True)
-- [(42,_.0),(_.1,True)]
disj :: Goal s x -> Goal s x -> Goal s x
disj left right = delay (newGoalScope (unsafeDisjunction left right))

-- | Perform disjunction of several goals, left to right.
--
-- >>> run (\x -> disjMany (map (\a -> x === Value a) [1, 3 .. 11 :: Int]))
-- [1,3,5,7,9,11]
disjMany :: [Goal s x] -> Goal s x
disjMany = delay . newGoalScope . foldr unsafeDisjunction failo

-- | Consider several possible cases, using syntax similar to @conde@ from
-- @faster-minikanren@.
--
-- >>> :{
--   run (\(x, y) -> conde
--     [ [ x === Value False, y === Value 0 ]
--     , [ x === Value True, y === Value 1 ]
--     ])
-- :}
-- [(False,0),(True,1)]
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
-- [(False,0),(True,1)]
--
-- In addition, the "Match" module provides pattern matching over variants,
-- which might better express your intent.
--
-- >>> :{
--   run (\(x, y) -> x & (matche
--     & on _False (\() -> y === Value 0)
--     & on _True (\() -> y === Value 1)))
-- :}
-- [(False,0),(True,1)]
conde :: [[Goal s ()]] -> Goal s ()
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
-- [(True,False)]
--
-- As an edge case, you can ask for no variables at all using @()@. While this
-- is not useful inside relations, this is how the first two examples actually
-- work. 'Fresh' is also used for pattern matching from the @"Match"@ module
-- when the matched value is not known yet.
class Fresh s v where
  -- | Create fresh variables.
  fresh :: Goal s v

  -- | Resolve each variable to its value in the given state. You won't need to
  -- use this method yourself, but 'run' uses it to return solutions.
  resolve :: State s -> v -> ST s v

instance Fresh s () where
  fresh = delay (return ())
  resolve _ () = return ()

-- | 'makeVariable' in the form of 'Goal'. Does not insert an 'Await' point,
-- while 'fresh' inserts a single point before creating all its variables.
fresh' :: Goal s (Term s a)
fresh' = Goal $ \state -> M (pure <$> makeVariable state)

instance (Logical a) => Fresh s (Term s a) where
  fresh = delay fresh'
  resolve = walk'

instance (Logical a, Fresh s v) => Fresh s (Term s a, v) where
  fresh = do
    v <- fresh
    a <- fresh'
    pure (a, v)
  resolve state (a, v) = do
    a' <- resolve state a
    v' <- resolve state v
    return (a', v')

instance (Logical a, Logical b, Fresh s v) => Fresh s (Term s a, Term s b, v) where
  fresh = do
    (b, v) <- fresh
    a <- fresh'
    pure (a, b, v)
  resolve state (a, b, v) = do
    a' <- resolve state a
    b' <- resolve state b
    v' <- resolve state v
    return (a', b', v')

instance
  (Logical a, Logical b, Logical c, Fresh s v)
  => Fresh s (Term s a, Term s b, Term s c, v)
  where
  fresh = do
    (b, c, v) <- fresh
    a <- fresh'
    pure (a, b, c, v)
  resolve state (a, b, c, v) = do
    a' <- resolve state a
    b' <- resolve state b
    c' <- resolve state c
    v' <- resolve state v
    return (a', b', c', v')

instance
  (Logical a, Logical b, Logical c, Logical d, Fresh s v)
  => Fresh s (Term s a, Term s b, Term s c, Term s d, v)
  where
  fresh = do
    (b, c, d, v) <- fresh
    a <- fresh'
    pure (a, b, c, d, v)
  resolve state (a, b, c, d, v) = do
    a' <- resolve state a
    b' <- resolve state b
    c' <- resolve state c
    d' <- resolve state d
    v' <- resolve state v
    return (a', b', c', d', v')

instance
  (Logical a, Logical b, Logical c, Logical d, Logical e, Fresh s v)
  => Fresh s (Term s a, Term s b, Term s c, Term s d, Term s e, v)
  where
  fresh = do
    (b, c, d, e, v) <- fresh
    a <- fresh'
    pure (a, b, c, d, e, v)
  resolve state (a, b, c, d, e, v) = do
    a' <- resolve state a
    b' <- resolve state b
    c' <- resolve state c
    d' <- resolve state d
    e' <- resolve state e
    v' <- resolve state v
    return (a', b', c', d', e', v')
