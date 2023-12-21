module Lib (Variable, Value(Unknown, Known), State, Term, (===), run) where

import Data.Maybe (maybeToList)

newtype Variable a = Variable Int deriving (Show, Eq)

data Value a = Unknown (Variable a) | Known a deriving (Show)

data State a = State [(Variable a, Value a)] (Variable a)

class Term a where
    unify :: a -> a -> State a -> Maybe (State a)

unifyEq :: Eq a => a -> a -> State a -> Maybe (State a)
unifyEq x y state
    | x == y = Just state
    | otherwise = Nothing

instance Term Bool where
    unify = unifyEq

instance Term Int where
    unify = unifyEq

instance Term Integer where
    unify = unifyEq

-- data LogicList a = Nil | Cons (Value a) (Value (LogicList a)) deriving (Show)
--
-- instance Term a => Term (LogicList a) where
--     unify Nil Nil state = Just state
--     unify (Cons x xs) (Cons y ys) state = unify x y state >>= unify xs ys

apply :: Value a -> State a -> Value a
apply value@(Known _) _ = value
apply (Unknown variable) (State values _) = case lookup variable values of
    Just value -> value
    Nothing -> Unknown variable

unify' :: Term a => Value a -> Value a -> State a -> Maybe (State a)
unify' left right state = case (left', right') of
    (Unknown left'', Unknown right'') | left'' == right'' -> Just state
    (Unknown variable, value) -> insert variable value
    (value, Unknown variable) -> insert variable value
    (Known left'', Known right'') -> unify left'' right'' state
  where
    left' = apply left state
    right' = apply right state

    State values nextVariable = state
    insert variable value =
        Just (State ((variable, value) : values) nextVariable)

type Goal a = State a -> [State a]

(===) :: Term a => Value a -> Value a -> Goal a
a === b = maybeToList . unify' a b

run :: (Value a -> Goal a) -> [Value a]
run f = map (apply initialVariable) (goal state)
  where
    state = State [] (Variable 1)
    initialVariable = Unknown (Variable 0)
    goal = f initialVariable

