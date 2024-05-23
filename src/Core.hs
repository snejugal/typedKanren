{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The very core of miniKanren. So core that it basically deals with
-- unification only. For writing relational programs, you will need @"Goal"@ as
-- well.
module Core (
  -- * Values and terms
  Logical (..),
  VarId,
  Term (..),

  -- ** Operations on terms
  unify',
  subst',
  inject',
  extract',

  -- * The search state
  State,
  empty,
  makeVariable,
  walk,
) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe)
import GHC.Exts (IsList (..))
import Unsafe.Coerce (unsafeCoerce)

-- | Types that can enter the relational world.
--
-- Simple types without fields, such as 'Bool' and 'Int', can be used in
-- relational programs as is. Instances for such types are as simple as
--
-- > data Ternary = True | False | Maybe deriving (Eq)
-- > instance Logical Ternary
--
-- >>> run (\x -> x === Value True)
-- [Value True]
--
-- When a type contains other types, this becomes more tricky. Consider the
-- following type:
--
-- > data Point = Point { x :: Int, y :: Int }
--
-- In the relational world, values may be known only partially. For example, we
-- may find out that some equation is true only for a particular value of @x@,
-- but once that holds, @y@ can be anything. The definition above cannot express
-- this, since @Point@ has to be instantiated with some particular pair of
-- @Int@s.
--
-- To account for this, we'd like to modify the definition slightly, so that
-- each field can possibly contain a variable:
--
-- > data LogicPoint = LogicPoint { logicX :: Term Int, logicY :: Term Int }
--
-- @'Term' a@ here can either be a 'Var' or a 'Value' for type @a@.
--
-- Now we can specify that a @Point@ becomes a @LogicPoint@ in the relational
-- world:
--
-- > instance Logical Point where
-- >   type Logic Point = LogicPoint
--
-- However, we are not finished here yet. When a type has a different
-- representation in the logical world, we need to show how we can go from
-- a @Point@ to a @LogicPoint@ with 'inject' and go back with 'extract':
--
-- > inject (Point x y) = LogicPoint (Value x) (Value y)
-- > extract (LogicPoint (Value x) (Value y)) = Just (Point x y)
-- > extract _ = Nothing
--
-- Note that while we can always transform a @Point@ to a @LogicPoint@, going
-- back to a @Point@ can fail if any field contains a variable.
--
-- We also need to show how @LogicPoint@s can be unified. For simple types,
-- unification of terms works in the following way. If both terms are already
-- known, we just check that they are equal. Otherwise, one of the terms is a
-- variable, and we record that it must be equal to the other term.
--
-- With complex types, a third case is possible: we can refine an existing value
-- if one of its fields is a variable. We can achieve this by unifying each
-- field separately.
--
-- > unify (LogicPoint leftX leftY) (LogicPoint rightX rightY) state =
-- >   unify' leftX rightX state >>= unify' leftY rightY
--
-- 'unify' takes two values being unified and the current state. If unification
-- succeeds, a new state with acquired knowledge is returned. if unification
-- leads to contradiction (the two values cannot be unified), 'unify' returns
-- 'Nothing'. You do not modify the state yourself — this is handled by
-- 'unify'', a version of 'unify' which works on 'Term's instead of logic
-- values.
--
-- When we find out that a variable must have a particular value, we need not
-- only to add a new entry in the state, but also update existing values which
-- might contain that variable. This is the job of 'subst', which takes
-- the value being updated and a function that maps variables to their current
-- value. Just like with 'unify', the actual job of replacing variables with
-- values is done by 'subst'', and you only need to apply it to each field.
--
-- > subst f (LogicPoint x y) = LogicPoint (subst' f x) (subst' f x)
--
-- You may notice that the logical representation of the type and the 'Logical'
-- instance are suitable for automatic generation. Indeed, the
-- @"GenericLogical"@ module provides generic versions of `Logical`'s methods.
-- The @"TH"@ module goes further and provides 'TH.makeLogic' to generate
-- logical representations for your types.
class Logical a where
  -- | The logical representation of this type. This defaults to the type
  -- itself, but complex types will usually have a separate logic type.
  --
  -- Note that 'Logic a' is injective, so two different types cannot use the
  -- same type as their logical representation. If you want to provide an
  -- instance for @newtype NT = NT T@, then the logical representation should be
  -- a newtype as well: @newtype LogicNT = LogicNT (Logic T)@.
  type Logic a = r | r -> a

  type Logic a = a

  -- | Perform unification of two values. If unification succeeds, return the
  -- possibly modified state. If unification leads to contradiction, return
  -- 'Nothing'.
  --
  -- The default implementation checks for equality, which works well for simple
  -- types. Complex types will provide their own implmentations which apply
  -- 'unify'' to each field.
  unify :: Logic a -> Logic a -> State -> Maybe State
  default unify :: (Eq (Logic a)) => Logic a -> Logic a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  -- | Update the value with acquired knowledge. This method takes a function
  -- which maps variables to its current known value.
  --
  -- The default implementation works for simple types and returns the value as
  -- is (since there's nothing to substitute inside). Complex types will provide
  -- their own implementations which apply 'subst'' to each field.
  subst :: (forall x. VarId x -> Maybe (Term x)) -> Logic a -> Logic a
  default subst :: (a ~ Logic a) => (forall x. VarId x -> Maybe (Term x)) -> Logic a -> Logic a
  subst _ = id

  -- | Transform a value to its logical representation.
  --
  -- The default implementation works for simple types and returns the value as
  -- is. Complex types will provide their own implementations which apply
  -- 'inject'' to each field. 'inject'' is also the function that you will use
  -- in your relational programs.
  inject :: a -> Logic a
  default inject :: (a ~ Logic a) => a -> Logic a
  inject = id

  -- | Transform a logical representation of a value back to its normal
  -- representation. Note that this transformation can fail in the general case,
  -- because variables cannot be transformed to values.
  --
  -- The default implementation works for simple types and returns the value as
  -- is. Complex types will provide their own implementations which apply
  -- 'extract'' to each field. 'extract'' is also the function that you will
  -- use in your code.
  extract :: Logic a -> Maybe a
  default extract :: (a ~ Logic a) => Logic a -> Maybe a
  extract = Just

-- | A variable, which reserves a place for a logical value for type @a@.
newtype VarId a = VarId Int
  deriving (Show, Eq)

-- | A logical value for type @a@, or a variable.
--
-- Note that @a@ must be the “normal” type, not its logical representation,
-- since 'Term' stores @'Logic' a@. For example, @Term (Either String (Tree
-- Int))@ will correctly use @LogicList Char@ and @LogicTree Int@ deep inside.
-- This way, you do not need to know what the logic representation for a type is
-- named, and deriving the logical representation for a type is trivial.
data Term a
  = Var (VarId a)
  | Value (Logic a)

deriving instance (Show (Logic a)) => Show (Term a)
deriving instance (Eq (Logic a)) => Eq (Term a)

instance (IsList (Logic a)) => IsList (Term a) where
  type Item (Term a) = Item (Logic a)
  fromList = Value . fromList

instance (Num (Logic a)) => Num (Term a) where
  fromInteger = Value . fromInteger

-- | 'unify', but on 'Term's instead of 'Logic' values. If new knowledge is
-- obtained during unification, it is obtained here.
unify' :: (Logical a) => Term a -> Term a -> State -> Maybe State
unify' l r state =
  case (walk state l, walk state r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst x r' state)
    (l', Var y) -> Just (addSubst y l' state)
    (Value l', Value r') -> unify l' r' state

-- | 'subst', but on 'Term's instead of 'Logic' values. The actual substitution
-- happens here.
subst' :: (Logical a) => (forall x. VarId x -> Maybe (Term x)) -> Term a -> Term a
subst' k (Value x) = Value (subst k x)
subst' k x@(Var i) = fromMaybe x (k i)

-- | 'inject', but to a 'Term' instead of a 'Logic' value. You will use this
-- function in your relational programs to inject normal values.
--
-- > run (\x -> x === inject' [1, 2, 3])
inject' :: (Logical a) => a -> Term a
inject' = Value . inject

-- | 'extract', but from a 'Term' instead of a 'Logic' value. Note that this
-- transformation can fail in the general case, because variables cannot be
-- transformed to values.
--
-- You will use this function to transform solutions of a program back to their
-- normal representation.
--
-- >>> extract' <$> run (\x -> x === inject' (Left 42))
-- [Just (Left 42)]
extract' :: (Logical a) => Term a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

-- | Since 'Term's are polymorphic, we cannot easily store them in the
-- substitution map. 'ErasedTerm' is the way to erase the type before putting
-- a 'Term' into the map.
data ErasedTerm where
  ErasedTerm :: (Logical a) => Term a -> ErasedTerm

instance Show ErasedTerm where
  show (ErasedTerm (Var varId)) = "Var " ++ show varId
  show (ErasedTerm (Value _)) = "Value _"

-- | Cast an 'ErasedTerm' back to a 'Term a'. Hopefully, you will cast it to the
-- correct type, or bad things will happen.
unsafeReconstructTerm :: ErasedTerm -> Term a
unsafeReconstructTerm (ErasedTerm x) = unsafeCoerce x

-- | Current knowledge of variable values.
newtype Subst = Subst (IntMap ErasedTerm) deriving (Show)

-- | One branch in the search tree. Keeps track of known substitutions and
-- variables.
data State = State
  { knownSubst :: !Subst
  , maxVarId :: !Int
  }
  deriving (Show)

-- | The initial state without any knowledge and variables.
empty :: State
empty = State{knownSubst = Subst IntMap.empty, maxVarId = 0}

-- | Create a variable in the given state.
makeVariable :: State -> (State, Term a)
makeVariable State{maxVarId, ..} = (state', var)
 where
  var = Var (VarId maxVarId)
  state' = State{maxVarId = maxVarId + 1, ..}

-- | Update the term using knowledge from the state.
walk :: (Logical a) => State -> Term a -> Term a
walk State{knownSubst} = apply knownSubst

apply :: (Logical a) => Subst -> Term a -> Term a
apply (Subst m) = subst' (\(VarId i) -> unsafeReconstructTerm <$> IntMap.lookup i m)

addSubst :: (Logical a) => VarId a -> Term a -> State -> State
addSubst (VarId i) value State{knownSubst = Subst m, ..} =
  State
    { knownSubst =
        Subst $
          IntMap.insert i (ErasedTerm value) $
            updateErasedTerm <$> m
    , ..
    }
 where
  updateErasedTerm (ErasedTerm x) =
    ErasedTerm (apply (Subst (IntMap.singleton i (ErasedTerm value))) x)
