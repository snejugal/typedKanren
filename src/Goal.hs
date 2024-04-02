{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}

module Goal (
  Goal,
  (===),
  conj,
  conjMany,
  disj,
  disjMany,
  conde,
  run,
  UnifiableFresh(..),
  fresh',
  matche
) where

import Control.Monad ((>=>))
import Control.Applicative (Alternative (..))
import qualified Data.Foldable as Foldable
import Data.Kind (Type)
import qualified Data.IntMap as IntMap

import Stream
import Core

newtype Goal (a :: Type) = Goal { runGoal :: State -> Stream State }

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
  empty = Goal (const Done)
  Goal g1 <|> Goal g2 =
    Goal (\state -> g1 state `interleave` g2 state)

(===) :: Unifiable a => ValueOrVar a -> ValueOrVar a -> Goal ()
a === b = Goal (maybeToStream . unify' a b)

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
run :: Unifiable a => (ValueOrVar a -> Goal ()) -> [ValueOrVar a]
run f = Foldable.toList (fmap resolveQueryVar (runGoal (f queryVar) initialState))
  where
    initialState = State
      { knownSubst = Subst IntMap.empty
      , maxVarId = 1
      }
    queryVar = Var (VarId 0)
    resolveQueryVar State{..} = apply knownSubst queryVar

class Unifiable a => UnifiableFresh a where
  fresh :: (Term a -> Goal ()) -> Goal ()

fresh' :: (ValueOrVar a -> Goal b) -> Goal b
fresh' f = Goal $ \State{..} ->
  let newState = State
        { maxVarId = maxVarId + 1
        , .. }
  in runGoal (f (Var (VarId maxVarId))) newState

matche :: UnifiableFresh a => ValueOrVar a -> (Term a -> Goal ()) -> Goal ()
matche (Value v) k = k v
matche x@Var{} k =
  fresh $ \v -> do
    x === Value v
    k v
