{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
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
) where

import           Control.DeepSeq
import           Control.Monad      (ap)
import           Data.Bifunctor     (first)
import           Data.Coerce        (coerce)
import           Data.Foldable      (foldrM)
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import           Data.Maybe         (fromMaybe)
import           GHC.Exts           (IsList (..))
import           GHC.Generics       (Generic)
import           Unsafe.Coerce      (unsafeCoerce)

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
class Eq a => Logical a where
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

  -- | Update the value with acquired knowledge. This method the current state
  -- to substitute variables with their obtained values.
  --
  -- The default implementation works for simple types and returns the value as
  -- is (since there's nothing to substitute inside). Complex types will provide
  -- their own implementations which apply 'walk'' to each field.
  walk :: State -> Logic a -> Logic a
  default walk :: (a ~ Logic a) => State -> Logic a -> Logic a
  walk _ = id

  occursCheck :: VarId b -> Logic a -> State -> Bool
  default occursCheck :: (a ~ Logic a) => VarId b -> Logic a -> State -> Bool
  occursCheck _ _ _ = False

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
  deriving newtype (Eq, NFData)

instance Show (VarId a) where
  show (VarId varId) = "_." ++ show varId

-- | A logical value for type @a@, or a variable.
--
-- Note that @a@ must be the “normal” type, not its logical representation,
-- since 'Term' stores @'Logic' a@. For example, @Term (Either String (Tree
-- Int))@ will correctly use @LogicList Char@ and @LogicTree Int@ deep inside.
-- This way, you do not need to know what the logic representation for a type is
-- named, and deriving the logical representation for a type is trivial.
data Term a
  = Var !(VarId a)
  | Value !(Logic a)
  | Injected !a
  deriving (Generic)

deriving instance (NFData a, NFData (Logic a)) => NFData (Term a)

instance (Eq a, Eq (Logic a), Logical a) => Eq (Term a) where
  Var x == Var y = x == y
  Value x == Value y = x == y
  Injected x == Injected y = x == y
  Injected x == Value y = inject x == y
  Value x == Injected y = x == inject y
  _ == _ = False

-- | This instance doesn't print the 'Var' and 'Value' tags. While this reduces
-- noise in the output, this may also be confusing since fully instantiated
-- terms may look indistinguishable from regular values.
instance (Show a, Show (Logic a)) => Show (Term a) where
  showsPrec d (Var var)     = showsPrec d var
  showsPrec d (Value value) = showsPrec d value
  showsPrec d (Injected x)  = showsPrec d x

instance (Logical a, IsList a, IsList (Logic a)) => IsList (Term a) where
  type Item (Term a) = Item (Logic a)
  fromList = Value . fromList
  toList (Value xs) = toList xs
  toList (Var x) = error ("cannot convert unification variable " <> show x <> " to list")
  toList (Injected x) = toList (inject x)

instance (Num a, Num (Logic a), Logical a) => Num (Term a) where
  fromInteger = Value . fromInteger
  (+) = unsafePromoteBinOp "(+)" (+) (+)
  (-) = unsafePromoteBinOp "(-)" (-) (-)
  (*) = unsafePromoteBinOp "(*)" (*) (*)
  abs = unsafePromoteUnaryOp "abs" abs abs
  signum = unsafePromoteUnaryOp "signum" signum signum
  negate = unsafePromoteUnaryOp "negate" negate negate

unsafePromoteUnaryOp :: String -> (a -> b) -> (Logic a -> Logic b) -> Term a -> Term b
unsafePromoteUnaryOp _name _f' f (Value x) = Value (f x)
unsafePromoteUnaryOp name _f' _f (Var x) = error ("cannot apply " <> name <> " to the unification variable " <> show x)
unsafePromoteUnaryOp _name f' _f (Injected x) = Injected (f' x)

unsafePromoteBinOp :: (Logical a, Logical b) => String -> (a -> b -> c) -> (Logic a -> Logic b -> Logic c) -> Term a -> Term b -> Term c
unsafePromoteBinOp _name _f' f (Value x) (Value y) = Value (f x y)
unsafePromoteBinOp _name f' _f (Injected x) (Injected y) = Injected (f' x y)
unsafePromoteBinOp _name _f' f (Injected x) (Value y) = Value (f (inject x) y)
unsafePromoteBinOp _name _f' f (Value x) (Injected y) = Value (f x (inject y))
unsafePromoteBinOp name _f' _f (Var x) _ = error ("cannot apply " <> name <> " to the unification variable " <> show x)
unsafePromoteBinOp name _f' _f _ (Var x) = error ("cannot apply " <> name <> " to the unification variable " <> show x)

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
unify' :: (Logical a) => Term a -> Term a -> State -> Maybe State
unify' l r state =
  case (shallowWalk state l, shallowWalk state r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r')
      | occursCheck' x r' state -> Nothing
      | otherwise -> addSubst x r' state
    (l', Var y)
      | occursCheck' y l' state -> Nothing
      | otherwise -> addSubst y l' state
    (Value l', Value r') -> unify l' r' state
    (Injected l', Injected r')
      | l' == r' -> Just state
      | otherwise -> Nothing
    (Injected l', Value r') -> unify (inject l') r' state
    (Value l', Injected r') -> unify l' (inject r') state

occursCheck' :: (Logical a) => VarId b -> Term a -> State -> Bool
occursCheck' x t state =
  case shallowWalk state t of
    Var y      -> coerce x == y
    Value v    -> occursCheck x v state
    Injected _ -> False -- there are no unification variables in injected values

-- | 'walk', but on 'Term's instead of 'Logic' values. The actual substitution
-- of variables with values happens here.
walk' :: (Logical a) => State -> Term a -> Term a
walk' state x = case shallowWalk state x of
  Var i        -> Var i
  Value v      -> Value (walk state v)
  t@Injected{} -> t -- there are no unification variables in injected values

-- | 'inject', but to a 'Term' instead of a 'Logic' value. You will use this
-- function in your relational programs to inject normal values.
--
-- > run (\x -> x === inject' [1, 2, 3])
inject' :: (Logical a) => a -> Term a
inject' = Injected

-- | 'extract', but from a 'Term' instead of a 'Logic' value. Note that this
-- transformation can fail in the general case, because variables cannot be
-- transformed to values.
--
-- You will use this function to transform solutions of a program back to their
-- normal representation.
--
-- >>> extract' <$> run (\x -> x === inject' (Left 42 :: Either Int Bool))
-- [Just (Left 42)]
extract' :: (Logical a) => Term a -> Maybe a
extract' Var{}        = Nothing
extract' (Value x)    = extract x
extract' (Injected x) = Just x

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
  normalize :: (forall i. VarId i -> Normalizer (VarId i)) -> Logic a -> Normalizer (Logic a)
  default normalize :: (a ~ Logic a) => (forall i. VarId i -> Normalizer (VarId i)) -> Logic a -> Normalizer (Logic a)
  normalize _ = pure

normalize' :: (Normalizable a) => (forall i. VarId i -> Normalizer (VarId i)) -> Term a -> Normalizer (Term a)
normalize' f (Var varId)  = Var <$> f varId
normalize' f (Value x)    = Value <$> normalize f x
normalize' _ t@Injected{} = pure t

runNormalize :: (Normalizable a) => Term a -> Term a
runNormalize x = normalized
 where
  Normalizer g = normalize' addVar x
  (_, normalized) = g (Normalization IntMap.empty 0)
  addVar (VarId varId) = Normalizer $ \n@(Normalization vars maxId) ->
    case IntMap.lookup varId vars of
      Just varId' -> (n, VarId varId')
      Nothing -> (Normalization vars' maxId', VarId maxId)
       where
        maxId' = maxId + 1
        vars' = IntMap.insert varId maxId vars

-- | Add a constraint that two terms must not be equal.
disequality :: (Logical a) => Term a -> Term a -> State -> Maybe State
disequality left right state = case addedSubst left right state of
  Nothing    -> Just state
  Just added -> stateInsertDisequality added state

-- | Since 'Term's are polymorphic, we cannot easily store them in the
-- substitution map. 'ErasedTerm' is the way to erase the type before putting
-- a 'Term' into the map.
data ErasedTerm where
  ErasedTerm :: (Logical a) => Term a -> ErasedTerm

instance Show ErasedTerm where
  show (ErasedTerm (Var varId))  = "Var " ++ show varId
  show (ErasedTerm (Value _))    = "Value _"
  show (ErasedTerm (Injected _)) = "Injected _"

-- | Cast an 'ErasedTerm' back to a 'Term a'. Hopefully, you will cast it to the
-- correct type, or bad things will happen.
unsafeReconstructTerm :: ErasedTerm -> Term a
unsafeReconstructTerm (ErasedTerm x) = unsafeCoerce x

-- | Current knowledge of variable values.
newtype Subst = Subst (IntMap ErasedTerm) deriving (Show)

substEmpty :: Subst
substEmpty = Subst IntMap.empty

substNull :: Subst -> Bool
substNull (Subst m) = IntMap.null m

-- | “Arbitrary” in the sense that this function decides which particular entry
-- to look up, but for the caller it's just some entry from the map. This
-- function must agree on this arbitrary entry with 'substExtractArbitrary'.
substLookupArbitraryId :: Subst -> Maybe Int
substLookupArbitraryId (Subst m) = fst <$> IntMap.lookupMin m

substExtractArbitrary :: Subst -> Maybe ((Int, ErasedTerm), Subst)
substExtractArbitrary (Subst m) = fmap Subst <$> IntMap.minViewWithKey m

addedSubst :: (Logical a) => Term a -> Term a -> State -> Maybe Subst
addedSubst left right state = knownSubst <$> unify' left' right' empty
 where
  left' = walk' state left
  right' = walk' state right

instance Semigroup Subst where
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
newtype Disequalities = Disequalities (IntMap [(ErasedTerm, Subst)])
  deriving (Show)

disequalitiesInsert :: Subst -> Disequalities -> Maybe Disequalities
disequalitiesInsert subst (Disequalities d) = do
  ((varId, value), subst') <- substExtractArbitrary subst
  let entry' = (value, subst') : fromMaybe [] (IntMap.lookup varId d)
  return (Disequalities (IntMap.insert varId entry' d))

disequalitiesExtract
  :: VarId a
  -> Disequalities
  -> Maybe ([(Term a, Subst)], Disequalities)
disequalitiesExtract (VarId varId) (Disequalities d) = do
  entry <- IntMap.lookup varId d
  let entry' = map (first unsafeReconstructTerm) entry

  let withoutEntry = Disequalities (IntMap.delete varId d)
  return (entry', withoutEntry)

disequalitiesUpdate
  :: (Logical a)
  => State
  -> VarId a
  -> Term a
  -> Disequalities
  -> Maybe Disequalities
disequalitiesUpdate state varId value d =
  case disequalitiesExtract varId d of
    Nothing -> Just d
    Just (varDisequalities, d') ->
      foldrM updateDisequality d' varDisequalities
 where
  value' = walk' state value
  updateDisequality (disallowedValue, subst) d' =
    case addedSubst value' disallowedValue state of
      Nothing -> Just d'
      Just added
        | substNull subst' -> Nothing
        | otherwise -> disequalitiesInsert subst' d'
       where
        subst' = updateComponents state (subst <> added)

updateComponents :: State -> Subst -> Subst
updateComponents state subst = case substExtractArbitrary subst of
  Nothing -> subst
  Just ((varId, ErasedTerm value), subst') ->
    case substLookupArbitraryId subst'' of
      Just varId' | varId == varId' -> subst''
      _                             -> updateComponents state subst''
   where
    added = fromMaybe substEmpty (addedSubst (Var (VarId varId)) value state)
    subst'' = subst' <> added

-- | One branch in the search tree. Keeps track of known substitutions and
-- variables.
data State = State
  { knownSubst    :: !Subst
  , disequalities :: !Disequalities
  , maxVarId      :: !Int
  }
  deriving (Show)

-- | The initial state without any knowledge and variables.
empty :: State
empty =
  State
    { knownSubst = substEmpty
    , disequalities = Disequalities IntMap.empty
    , maxVarId = 0
    }

-- | Create a variable in the given state.
makeVariable :: State -> (State, Term a)
makeVariable State{maxVarId, ..} = (state', var)
 where
  var = Var (VarId maxVarId)
  state' = State{maxVarId = maxVarId + 1, ..}

shallowWalk :: (Logical a) => State -> Term a -> Term a
shallowWalk _ t@Value{} = t
shallowWalk _ t@Injected{} = t
shallowWalk state@State{knownSubst = Subst m} (Var (VarId i)) =
  case IntMap.lookup i m of
    Nothing -> Var (VarId i)
    Just v  -> shallowWalk state (unsafeReconstructTerm v)

addSubst :: (Logical a) => VarId a -> Term a -> State -> Maybe State
addSubst (VarId i) value State{knownSubst = Subst m, ..} =
  stateUpdateDisequalities (VarId i) value $
    State
      { knownSubst = Subst $ IntMap.insert i (ErasedTerm value) m
      , ..
      }

stateInsertDisequality :: Subst -> State -> Maybe State
stateInsertDisequality subst state@State{disequalities} = do
  disequalities' <- disequalitiesInsert subst disequalities
  return state{disequalities = disequalities'}

stateUpdateDisequalities
  :: (Logical a)
  => VarId a
  -> Term a
  -> State
  -> Maybe State
stateUpdateDisequalities varId value state@State{disequalities} = do
  disequalities' <- disequalitiesUpdate state varId value disequalities
  return (state{disequalities = disequalities'})
