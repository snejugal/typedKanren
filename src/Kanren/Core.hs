{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | The very core of miniKanren. So core that it basically deals with
-- unification only. For writing relational programs, you will need @"Goal"@ as
-- well.
module Kanren.Core (
  -- * Values and terms
  Logical (..),
  VarId,
  Term (..),
  Atomic (..),

  -- ** Operations on terms
  unify',
  walk',
  occursCheck',
  inject',
  extract',
  Normalizable (..),
  normalize',
  runNormalize,

  -- ** Constraints
  disequality,

  -- * The search state
  State,
  empty,
  makeVariable,
  newScope,
) where

import Control.DeepSeq
import Control.Monad (ap)
import Control.Monad.ST (ST)
import Data.Bifunctor (first)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromMaybe)
import Data.STRef.Strict (STRef, modifySTRef', newSTRef, readSTRef, writeSTRef)
import Data.Tagged (Tagged (Tagged, unTagged))
import GHC.Exts (IsList (..))
import GHC.Generics (Generic)
import Unsafe.Coerce (unsafeCoerce)

-- $setup
-- >>> :set -package typedKanren
-- >>> import Kanren.Goal
-- >>> import Kanren.LogicalBase

-- | Types that can enter the relational world.
--
-- Simple types without fields, such as 'Bool' and 'Int', can be used in
-- relational programs as is. Instances for such types are as simple as
--
-- > data Ternary = True | False | Maybe deriving (Eq)
-- > instance Logical Ternary
--
-- >>> run (\x -> x === Value True)
-- [True]
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
-- might contain that variable. This is the job of 'walk', which takes the value
-- being updated and the current state. Just like with 'unify', the actual job
-- of replacing variables with values is done by 'walk'', and you only need to
-- apply it to each field.
--
-- > walk f (LogicPoint x y) = LogicPoint (walk' f x) (walk' f x)
--
-- You may notice that the logical representation of the type and the 'Logical'
-- instance are suitable for automatic generation. Indeed, the
-- @"GenericLogical"@ module provides generic versions of `Logical`'s methods.
-- The @"TH"@ module goes further and provides 'TH.makeLogic' to generate
-- logical representations for your types.
--
-- Although you'll see instances for @base@ types below, keep in mind that
-- they're only available from the @"LogicalBase"@ module.
class Logical a where
  -- | The logical representation of this type. This defaults to the type
  -- itself, but complex types will usually have a separate logic type.
  --
  -- Note that 'Logic a' is injective, so two different types cannot use the
  -- same type as their logical representation. If you want to provide an
  -- instance for @newtype NT = NT T@, then the logical representation should be
  -- a newtype as well: @newtype LogicNT = LogicNT (Logic T)@.
  type Logic s a = r | r -> s a

  type Logic s a = Tagged s a

  -- | Perform unification of two values. If unification succeeds, return the
  -- possibly modified state. If unification leads to contradiction, return
  -- 'Nothing'.
  --
  -- The default implementation checks for equality, which works well for simple
  -- types. Complex types will provide their own implmentations which apply
  -- 'unify'' to each field.
  unify :: Logic s a -> Logic s a -> State s -> ST s (Maybe (State s))
  default unify :: (Eq (Logic s a)) => Logic s a -> Logic s a -> State s -> ST s (Maybe (State s))
  unify x y state
    | x == y = return (Just state)
    | otherwise = return Nothing

  -- | Update the value with acquired knowledge. This method the current state
  -- to substitute variables with their obtained values.
  --
  -- The default implementation works for simple types and returns the value as
  -- is (since there's nothing to substitute inside). Complex types will provide
  -- their own implementations which apply 'walk'' to each field.
  walk :: State s -> Logic s a -> ST s (Logic s a)
  default walk :: (Logic s a ~ Tagged s a) => State s -> Logic s a -> ST s (Logic s a)
  walk _ = return

  occursCheck :: Var s b -> Logic s a -> State s -> ST s Bool
  default occursCheck :: (Logic s a ~ Tagged s a) => Var s b -> Logic s a -> State s -> ST s Bool
  occursCheck _ _ _ = return False

  -- | Transform a value to its logical representation.
  --
  -- The default implementation works for simple types and returns the value as
  -- is. Complex types will provide their own implementations which apply
  -- 'inject'' to each field. 'inject'' is also the function that you will use
  -- in your relational programs.
  inject :: a -> Logic s a
  default inject :: (Logic s a ~ Tagged s a) => a -> Logic s a
  inject = Tagged

  -- | Transform a logical representation of a value back to its normal
  -- representation. Note that this transformation can fail in the general case,
  -- because variables cannot be transformed to values.
  --
  -- The default implementation works for simple types and returns the value as
  -- is. Complex types will provide their own implementations which apply
  -- 'extract'' to each field. 'extract'' is also the function that you will
  -- use in your code.
  extract :: Logic s a -> Maybe a
  default extract :: (Logic s a ~ Tagged s a) => Logic s a -> Maybe a
  extract = Just . unTagged

-- | A variable, which reserves a place for a logical value for type @a@.
newtype VarId a = VarId Int
  deriving newtype (Eq, NFData)

instance Show (VarId a) where
  show (VarId varId) = "_." ++ show varId

newtype Scope = Scope Int deriving newtype (Eq, Show, NFData)

nonLocalScope :: Scope
nonLocalScope = Scope 0

initialScope :: Scope
initialScope = Scope 1

data Var s a = MkVar
  { varId :: !(VarId a)
  -- ^ Variable ID
  , varScope :: !Scope
  -- ^ Scope in which the variable was created
  , varValue :: !(STRef s (Maybe (Term s a)))
  -- ^ Value of the variable, if set-var-val was applied
  }

instance Eq (Var s a) where
  MkVar i _ _ == MkVar j _ _ = i == j

instance Show (Var s a) where
  show (MkVar varId _ _) = show varId

instance NFData (Var s a) where
  rnf (MkVar varId scope value) = rnf varId `seq` rnf scope `seq` rnf value

-- | A logical value for type @a@, or a variable.
--
-- Note that @a@ must be the “normal” type, not its logical representation,
-- since 'Term' stores @'Logic' a@. For example, @Term (Either String (Tree
-- Int))@ will correctly use @LogicList Char@ and @LogicTree Int@ deep inside.
-- This way, you do not need to know what the logic representation for a type is
-- named, and deriving the logical representation for a type is trivial.
data Term s a
  = Var !(Var s a)
  | Value !(Logic s a)
  deriving (Generic)

deriving instance (NFData (Logic s a)) => NFData (Term s a)

deriving instance (Eq (Logic s a)) => Eq (Term s a)

-- | This instance doesn't print the 'Var' and 'Value' tags. While this reduces
-- noise in the output, this may also be confusing since fully instantiated
-- terms may look indistinguishable from regular values.
instance (Show (Logic s a)) => Show (Term s a) where
  showsPrec d (Var var) = showsPrec d var
  showsPrec d (Value value) = showsPrec d value

instance (IsList (Logic s a)) => IsList (Term s a) where
  type Item (Term s a) = Item (Logic s a)
  fromList = Value . fromList
  toList (Value xs) = toList xs
  toList (Var x) = error ("cannot convert unification variable " <> show x <> " to list")

instance (Num (Logic s a)) => Num (Term s a) where
  fromInteger = Value . fromInteger
  (+) = unsafePromoteBinOp "(+)" (+)
  (-) = unsafePromoteBinOp "(-)" (-)
  (*) = unsafePromoteBinOp "(*)" (*)
  abs = unsafePromoteUnaryOp "abs" abs
  signum = unsafePromoteUnaryOp "signum" signum
  negate = unsafePromoteUnaryOp "negate" negate

unsafePromoteUnaryOp :: String -> (Logic s a -> Logic s b) -> Term s a -> Term s b
unsafePromoteUnaryOp _name f (Value x) = Value (f x)
unsafePromoteUnaryOp name _f (Var x) = error ("cannot apply " <> name <> " to the unification variable " <> show x)

unsafePromoteBinOp :: String -> (Logic s a -> Logic s b -> Logic s c) -> Term s a -> Term s b -> Term s c
unsafePromoteBinOp _name f (Value x) (Value y) = Value (f x y)
unsafePromoteBinOp name _f (Var x) _ = error ("cannot apply " <> name <> " to the unification variable " <> show x)
unsafePromoteBinOp name _f _ (Var x) = error ("cannot apply " <> name <> " to the unification variable " <> show x)

-- | Treat a type as atomic, i.e. containing no variables inside. This requires
-- @a@ only to have an 'Eq' instance, thus ignoring its logical representation
-- if it exists. Useful when you really don't want to look inside something.
--
-- > type Symbol = Atomic String
newtype Atomic a = Atomic a
  deriving newtype (Eq, NFData)

instance (Eq a) => Logical (Atomic a)
instance (Show a) => Show (Atomic a) where
  show (Atomic x) = show x
instance (Eq a) => Normalizable (Atomic a)

-- | 'unify', but on 'Term's instead of 'Logic' values. If new knowledge is
-- obtained during unification, it is obtained here.
unify' :: (Logical a) => Term s a -> Term s a -> State s -> ST s (Maybe (State s))
unify' left right state = do
  left' <- shallowWalk state left
  right' <- shallowWalk state right
  case (left', right') of
    (Var x, Var y)
      | x == y -> return (Just state)
    (Var x, r') -> addSubst x r' state
    (l', Var y) -> addSubst y l' state
    (Value l', Value r') -> unify l' r' state

occursCheck' :: (Logical a) => Var s b -> Term s a -> State s -> ST s Bool
occursCheck' x@(MkVar (VarId i) _ _) term state =
  shallowWalk state term >>= \case
    Var (MkVar{varId = VarId j}) -> return (i == j)
    Value v -> occursCheck x v state

-- | 'walk', but on 'Term s's instead of 'Logic' values. The actual substitution
-- of variables with values happens here.
walk' :: (Logical a) => State s -> Term s a -> ST s (Term s a)
walk' state term =
  shallowWalk state term >>= \case
    Var var -> return (Var var)
    Value v -> Value <$> walk state v

-- | 'inject', but to a 'Term s' instead of a 'Logic' value. You will use this
-- function in your relational programs to inject normal values.
--
-- > run (\x -> x === inject' [1, 2, 3])
inject' :: (Logical a) => a -> Term s a
inject' = Value . inject

-- | 'extract', but from a 'Term s' instead of a 'Logic' value. Note that this
-- transformation can fail in the general case, because variables cannot be
-- transformed to values.
--
-- You will use this function to transform solutions of a program back to their
-- normal representation.
--
-- >>> extract' <$> run (\x -> x === inject' (Left 42 :: Either Int Bool))
-- [Just (Left 42)]
extract' :: (Logical a) => Term s a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

data Normalization = Normalization (IntMap Int) Int
newtype Normalizer a = Normalizer (Normalization -> (Normalization, a)) deriving (Functor)

instance Applicative Normalizer where
  pure x = Normalizer (,x)
  (<*>) = ap

instance Monad Normalizer where
  return = pure
  Normalizer f >>= g = Normalizer $ \state ->
    let (state', x) = f state
        Normalizer h = g x
     in h state'

class (Logical a) => Normalizable a where
  normalize
    :: (forall i. Var s i -> Normalizer (Var s i))
    -> Logic s a
    -> Normalizer (Logic s a)
  default normalize
    :: (Logic s a ~ Tagged s a)
    => (forall i. Var s i -> Normalizer (Var s i))
    -> Logic s a
    -> Normalizer (Logic s a)
  normalize _ = pure

normalize'
  :: (Normalizable a)
  => (forall i. Var s i -> Normalizer (Var s i))
  -> Term s a
  -> Normalizer (Term s a)
normalize' f (Var var) = Var <$> f var
normalize' f (Value x) = Value <$> normalize f x

runNormalize :: (Normalizable a) => Term s a -> Term s a
runNormalize x = normalized
 where
  Normalizer g = normalize' addVar x
  (_, normalized) = g (Normalization IntMap.empty 0)
  addVar (MkVar (VarId varId) age value) = Normalizer $ \n@(Normalization vars maxId) ->
    case IntMap.lookup varId vars of
      Just varId' -> (n, MkVar (VarId varId') age value)
      Nothing -> (Normalization vars' maxId', MkVar (VarId maxId) age value)
       where
        maxId' = maxId + 1
        vars' = IntMap.insert varId maxId vars

-- | Add a constraint that two terms must not be equal.
disequality :: (Logical a) => Term s a -> Term s a -> State s -> ST s (Maybe (State s))
disequality left right state =
  addedSubst left right state >>= \case
    Nothing -> return (Just state)
    Just added -> stateInsertDisequality added state

-- | Since 'Term's are polymorphic, we cannot easily store them in the
-- substitution map. 'ErasedTerm' is the way to erase the type before putting
-- a 'Term' into the map.
data ErasedTerm s where
  ErasedTerm :: (Logical a) => Term s a -> ErasedTerm s

instance Show (ErasedTerm s) where
  show (ErasedTerm (Var varId)) = "Var " ++ show varId
  show (ErasedTerm (Value _)) = "Value _"

-- | Cast an 'ErasedTerm' back to a 'Term a'. Hopefully, you will cast it to the
-- correct type, or bad things will happen.
unsafeReconstructTerm :: ErasedTerm s -> Term s a
unsafeReconstructTerm (ErasedTerm x) = unsafeCoerce x

-- | Current knowledge of variable values.
newtype Subst s = Subst (IntMap (ErasedTerm s)) deriving (Show)

substEmpty :: Subst s
substEmpty = Subst IntMap.empty

substInsert :: (Logical a) => VarId a -> Term s a -> Subst s -> Subst s
substInsert (VarId i) value (Subst m) = Subst (IntMap.insert i (ErasedTerm value) m)

-- | “Arbitrary” in the sense that this function decides which particular entry
-- to look up, but for the caller it's just some entry from the map. This
-- function must agree on this arbitrary entry with 'substExtractArbitrary'.
substLookupArbitraryId :: Subst s -> Maybe Int
substLookupArbitraryId (Subst m) = fst <$> IntMap.lookupMin m

substExtractArbitrary :: Subst s -> Maybe ((Int, ErasedTerm s), Subst s)
substExtractArbitrary (Subst m) = fmap Subst <$> IntMap.minViewWithKey m

addedSubst :: (Logical a) => Term s a -> Term s a -> State s -> ST s (Maybe (Subst s))
addedSubst left right state = do
  left' <- walk' state left
  right' <- walk' state right
  fmap knownSubst <$> unify' left' right' emptied
 where
  emptied =
    State
      { knownSubst = substEmpty
      , scope = nonLocalScope
      , globalScope = globalScope state
      , disequalities = disequalitiesEmpty
      , maxVarId = maxVarId state
      }

instance Semigroup (Subst s) where
  Subst l <> Subst r = Subst (l <> r)

-- | Disequality constraints.
--
-- We try to perform the same optimization as @faster-minikanren@ does. If
-- we meet a constraint @(x, y) =/= (1, 2)@, we can transform it to
-- @x /= 1 || y /= 2@. But note that every disequality must be falsified for the
-- constraint to fail. Hence we do not need to attach this constraint to every
-- variable; we only need to pick one variable and attach the whole constraint
-- to it.
--
-- > x => [(1, y => 2)]
--
-- Together with the disallowed value for @x@, we store a map with the rest of
-- disequalities for this constraint. If we find that @x@ is 1, we merge that
-- map into 'Disequalities'. If that map is empty however, it means that the
-- constraint must fail. If we first learn that @y@ is 2, we don't care until
-- @x /= 1@ is falsified.
--
-- If there are several constraints on @x@, they'll be stored in a list.
--
-- > x => [(1, y => 2), (2, empty)]
--
-- If @x@ turns out to be 1, there are still other disequalities to check,
-- but if @x@ becomes 2, then we fail. If @x@ is anything else, we just drop
-- all constraints attached to it.
newtype Disequalities s = Disequalities (IntMap [(ErasedTerm s, Subst s)])
  deriving (Show)

disequalitiesEmpty :: Disequalities s
disequalitiesEmpty = Disequalities IntMap.empty

disequalitiesInsert :: Subst s -> Disequalities s -> Maybe (Disequalities s)
disequalitiesInsert subst (Disequalities d) = do
  ((varId, value), subst') <- substExtractArbitrary subst
  let entry' = (value, subst') : fromMaybe [] (IntMap.lookup varId d)
  return (Disequalities (IntMap.insert varId entry' d))

disequalitiesExtract
  :: VarId a
  -> Disequalities s
  -> Maybe ([(Term s a, Subst s)], Disequalities s)
disequalitiesExtract (VarId varId) (Disequalities d) = do
  entry <- IntMap.lookup varId d
  let entry' = map (first unsafeReconstructTerm) entry

  let withoutEntry = Disequalities (IntMap.delete varId d)
  return (entry', withoutEntry)

disequalitiesUpdate
  :: (Logical a)
  => State s
  -> VarId a
  -> Term s a
  -> Disequalities s
  -> ST s (Maybe (Disequalities s))
disequalitiesUpdate state varId value d =
  case disequalitiesExtract varId d of
    Nothing -> return (Just d)
    Just (varDisequalities, d') -> go varDisequalities d'
 where
  go [] d' = return (Just d')
  go ((disallowedValue, subst) : rest) d' = do
    added <- addedSubst value disallowedValue state
    case added of
      Nothing -> return (Just d')
      Just added' -> do
        subst' <- updateComponents state (subst <> added')
        -- TODO: remove comment if actually useless
        -- if substNull subst'
        --   then return Nothing
        --   else
        case disequalitiesInsert subst' d' of
          Nothing -> return Nothing
          Just d'' -> go rest d''

updateComponents :: State s -> Subst s -> ST s (Subst s)
updateComponents state subst = case substExtractArbitrary subst of
  Nothing -> return subst
  Just ((varId, ErasedTerm value), subst') -> do
    varValue <- newSTRef Nothing
    let thisVar = Var (MkVar (VarId varId) initialScope varValue)
    added <- fromMaybe substEmpty <$> addedSubst thisVar value state
    let subst'' = subst' <> added
    case substLookupArbitraryId subst'' of
      Just varId' | varId == varId' -> return subst''
      _ -> updateComponents state subst''

-- | One branch in the search tree. Keeps track of known substitutions and
-- variables.
data State s = State
  { knownSubst :: !(Subst s)
  , scope :: !Scope
  , globalScope :: !(STRef s Scope)
  , disequalities :: !(Disequalities s)
  , maxVarId :: !Int
  }

instance Show (State s) where
  show (State{knownSubst, scope, disequalities, maxVarId}) =
    "State{knownSubst="
      <> show knownSubst
      <> ", scope="
      <> show scope
      <> ", globalScope=(STRef), disequalities="
      <> show disequalities
      <> ", maxVarId="
      <> show maxVarId
      <> " }"

-- | The initial state without any knowledge and variables.
empty :: ST s (State s)
empty = do
  globalScope <- newSTRef initialScope
  return $
    State
      { knownSubst = substEmpty
      , scope = initialScope
      , globalScope
      , disequalities = Disequalities IntMap.empty
      , maxVarId = 0
      }

newScope :: State s -> ST s (State s)
newScope state@State{globalScope} = do
  modifySTRef' globalScope (\(Scope x) -> Scope (x + 1))
  scope' <- readSTRef globalScope
  return state{scope = scope'}

-- | Create a variable in the given state.
makeVariable :: State s -> ST s (State s, Term s a)
makeVariable state@State{maxVarId, scope} = do
  value <- newSTRef Nothing
  let var = Var (MkVar (VarId maxVarId) scope value)
  let state' = state{maxVarId = maxVarId + 1}
  return (state', var)

shallowWalk :: (Logical a) => State s -> Term s a -> ST s (Term s a)
shallowWalk _ (Value v) = return (Value v)
shallowWalk state@State{knownSubst = Subst m} var@(Var MkVar{varId = VarId i, varValue}) = do
  varValue' <- readSTRef varValue
  case varValue' of
    Just v -> shallowWalk state v
    Nothing -> case IntMap.lookup i m of
      Just v -> shallowWalk state (unsafeReconstructTerm v)
      Nothing -> return var

addSubst :: (Logical a) => Var s a -> Term s a -> State s -> ST s (Maybe (State s))
addSubst MkVar{varId, varScope, varValue} value state@State{knownSubst, scope}
  | varScope == scope = do
      -- NOTE: if the variable were to participate in a disequality, its
      -- scope would be different and this branch would not be taken
      writeSTRef varValue (Just value)
      return (Just state)
  | otherwise = stateUpdateDisequalities varId value state'
 where
  state' = state{knownSubst = substInsert varId value knownSubst}

stateInsertDisequality :: Subst s -> State s -> ST s (Maybe (State s))
stateInsertDisequality subst state@State{disequalities} = do
  let state' = fmap (\d -> state{disequalities = d}) (disequalitiesInsert subst disequalities)
  case state' of
    Nothing -> return Nothing
    -- TODO: incrementing the scope is necessary for now because the STRef is
    -- not saved in disequalities, and it would be bad if we couldn't access
    -- a variable's value assigned in-place
    Just s -> Just <$> newScope s

stateUpdateDisequalities
  :: (Logical a)
  => VarId a
  -> Term s a
  -> State s
  -> ST s (Maybe (State s))
stateUpdateDisequalities varId value state@State{disequalities} = do
  disequalitiesUpdate state varId value disequalities >>= \case
    Nothing -> return Nothing
    Just disequalities' -> return (Just state{disequalities = disequalities'})
