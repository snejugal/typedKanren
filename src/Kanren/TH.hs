{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Automatic generation of logic types.
module Kanren.TH (
  makeLogical,
  makeLogicals,

  -- * Logic representations
  makeLogicType,
  makeLogicTypes,
  LogicTypeRules,
  defaultLogicTypeRules,
  makeLogicTypeWith,
  makeLogicTypesWith,

  -- * 'Logical' instances
  makeLogicalInstance,
  makeLogicalInstances,
) where

import Data.Char (isUpper, toUpper)
import Data.Foldable (foldl')
import GHC.Generics (Generic)
import Language.Haskell.TH hiding (bang)

import Kanren.Core
import Kanren.GenericLogical

-- | Generate a logic representation and a corresponding 'Logical' instance for
-- a given type.
--
-- Using this function requires you to enable the @DeriveGeneric@ and
-- @TypeFamilies@ extensions.
--
-- Consider the following type definition:
--
-- > data Tree a
-- >   = Empty
-- >   | Leaf a
-- >   | Tree a :* Tree a
--
-- @makeLogical ''Tree@ yields
--
-- > data LogicTree a
-- >   = LogicEmpty
-- >   | LogicLeaf (Term a)
-- >   | Term (Tree a) :?* Term (Tree a)
-- >   deriving (Generic)
-- >
-- > instance Logical a => Logical (Tree a) where
-- >   type Logic (Tree a) = LogicTree a
-- >   unify = genericUnify
-- >   walk = genericWalk
-- >   occursCheck = genericOccursCheck
-- >   inject = genericInject
-- >   extract = genericExtract
--
-- For details, see 'makeLogicType' and 'makeLogicalInstance'.
makeLogical :: Name -> Q [Dec]
makeLogical name = do
  logicType <- makeLogicTypeWith logicTypeRules name
  logicalInstance <- makeLogicalInstance name (logicName name)
  return (logicType <> logicalInstance)
 where
  logicTypeRules = defaultLogicTypeRules{derives = [ConT ''Generic]}

-- | Generate a logic representation and a corresponding 'Logical' instance for
-- each given type. This works like 'makeLogical', but better suits mutually
-- recursive types.
makeLogicals :: [Name] -> Q [Dec]
makeLogicals = foldMap makeLogical

-- | Settings for generating a type's logic representation.
newtype LogicTypeRules = LogicTypeRules
  { derives :: [Type]
  -- ^ Instances that should be derived for the logical representation.
  }

-- | Default 'LogicTypeRules'. Does not derive any instances for the logical
-- representation.
defaultLogicTypeRules :: LogicTypeRules
defaultLogicTypeRules = LogicTypeRules{derives = []}

-- | Generate a logic representation for a given type.
--
-- Consider the following type definition:
--
-- > data Tree a
-- >   = Empty
-- >   | Leaf a
-- >   | Tree a :* Tree a
--
-- @makeLogicType ''Tree@ yields
--
-- > data LogicTree a
-- >   = LogicEmpty
-- >   | LogicLeaf (Term a)
-- >   | Term (Tree a) :?* Term (Tree a)
--
-- For @newtype@s, it doesn't make sense to introduce another layer of
-- variables. Hence, 'Logic' will be used instead of 'Term'.
--
-- > newtype BetterInt = BetterInt Int
-- > makeLogicType ''BetterInt
-- > -- ^ newtype LogicBetterInt = LogicBetterInt (Logic Int)
makeLogicType :: Name -> Q [Dec]
makeLogicType = makeLogicTypeWith defaultLogicTypeRules

-- | 'makeLogicType', but allows configuring how the logical representation is
-- generated.
makeLogicTypeWith :: LogicTypeRules -> Name -> Q [Dec]
makeLogicTypeWith (LogicTypeRules{derives}) name = do
  TyConI declaration <- reify name
  let deriv
        | null derives = []
        | otherwise = [DerivClause Nothing derives]

  logicType <- case declaration of
    -- data T = A B ==> data LogicT = LogicA (Term B)
    DataD constraints _ variables kind constructors _ -> do
      let name' = logicName name
      let constructors' = logicConstructors ''Term constructors
      return (DataD constraints name' variables kind constructors' deriv)
    -- newtype T = A B = newtype LogicT = LogicA (Logic B)
    NewtypeD constraints _ variables kind constructor _ -> do
      let name' = logicName name
      let constructor' = logicConstructor ''Logic constructor
      return (NewtypeD constraints name' variables kind constructor' deriv)
    other -> fail ("Expected a `data` or `newtype` declaration, but got:\n" <> show other)

  return [logicType]

-- | Generate a logic representation for several types. This works like
-- 'makeLogicType', but better suits mutually recursive types.
makeLogicTypes :: [Name] -> Q [Dec]
makeLogicTypes = foldMap makeLogicType

-- | 'makeLogicTypes', but allows configuring how the logical representations
-- are generated.
makeLogicTypesWith :: LogicTypeRules -> [Name] -> Q [Dec]
makeLogicTypesWith = foldMap . makeLogicTypeWith

-- | Generate a logic name for any name. @Tree@ becomes @LogicTree@, @age@
-- becomes @logicAge@, @:^@ becomes @:?^@.
logicName :: Name -> Name
logicName name = mkName $ case nameBase name of
  "" -> ""
  ':' : rest -> ":?" <> rest
  firstLetter : rest
    | isUpper firstLetter -> "Logic" <> rest'
    | otherwise -> "logic" <> rest'
   where
    rest' = toUpper firstLetter : rest

logicNames :: [Name] -> [Name]
logicNames = map logicName

logicConstructor :: Name -> Con -> Con
-- C Int a ==> LogicC (Term Int) (Term a)
logicConstructor wrapper (NormalC name fields) =
  NormalC (logicName name) (wrapBangTypes wrapper fields)
-- C { v :: Int, w :: a } ==>
-- LogicC { logicV :: Term Int, logicW :: Term a }
logicConstructor wrapper (RecC name fields) =
  RecC (logicName name) (wrapVarBangTypes wrapper fields)
-- Int :+ a ==> Term Int :?+ Term a
logicConstructor wrapper (InfixC left name right) =
  InfixC left' (logicName name) right'
 where
  left' = wrapBangType wrapper left
  right' = wrapBangType wrapper right
-- forall a. Eq a => C ... ==> forall a. Eq a => LogicC ...
logicConstructor wrapper (ForallC vars constraints constructor) =
  ForallC vars constraints (logicConstructor wrapper constructor)
-- C1, C2 :: a -> T b ==> LogicC1, LogicC2 :: Term a -> LogicT b
logicConstructor wrapper (GadtC names fields returnType) =
  GadtC (logicNames names) (wrapBangTypes wrapper fields) (logicGadt returnType)
-- C1, C2 :: { v :: Int } -> T b ==>
-- LogicC1, LogicC2 :: { logicV :: Term Int } -> LogicT b
logicConstructor wrapper (RecGadtC names fields returnType) =
  RecGadtC (logicNames names) (wrapVarBangTypes wrapper fields) (logicGadt returnType)

logicConstructors :: Name -> [Con] -> [Con]
logicConstructors = map . logicConstructor

wrapType :: Name -> Type -> Type
wrapType = AppT . ConT

wrapBangType :: Name -> BangType -> BangType
wrapBangType = fmap . wrapType

wrapBangTypes :: Name -> [BangType] -> [BangType]
wrapBangTypes = map . wrapBangType

wrapVarBangType :: Name -> VarBangType -> VarBangType
wrapVarBangType wrapper (name, bang, typ) =
  (logicName name, bang, wrapType wrapper typ)

wrapVarBangTypes :: Name -> [VarBangType] -> [VarBangType]
wrapVarBangTypes = map . wrapVarBangType

logicGadt :: Type -> Type
-- forall a. Eq a => T ==> forall a. Eq a => LogicT
logicGadt (ForallT vars constraints typ) =
  ForallT vars constraints (logicGadt typ)
-- forall a -> T ==> forall a -> LogicT
logicGadt (ForallVisT vars typ) = ForallVisT vars typ
-- T a ==> LogicT a
logicGadt (AppT typ arg) = AppT (logicGadt typ) arg
-- T @k ==> LogicT @k
logicGadt (AppKindT typ kind) = AppT (logicGadt typ) kind
logicGadt (VarT var) = VarT var
-- T ==> LogicT
logicGadt (ConT name) = ConT (logicName name)
-- 'T ==> 'LogicT
logicGadt (PromotedT name) = PromotedT (logicName name)
-- A :+ B ==> A :?+ B
logicGadt (InfixT left name right) = InfixT left (logicName name) right
logicGadt (UInfixT left name right) = UInfixT left (logicName name) right
-- A :+: B ==> A :?+: B
logicGadt (PromotedInfixT left name right) =
  PromotedInfixT left (logicName name) right
logicGadt (PromotedUInfixT left name right) =
  PromotedUInfixT left (logicName name) right
-- (T) ==> (LogicT)
logicGadt (ParensT typ) = ParensT (logicGadt typ)
-- ?x :: T ===> ?x :: LogicT
logicGadt (ImplicitParamT param typ) = ImplicitParamT param (logicGadt typ)
logicGadt other = other -- give up. shouldn't appear in a GADT anyway

-- | Generate a 'Logical' instance, given a type and its logical representation.
--
-- Currently, the instance relies on @"GenericLogical"@, so both types need to
-- have a 'Generic' instance. When using 'makeLogical', the logical
-- representation will have a derived 'Generic' instance.
--
-- For each type variable, there will be a 'Logical' constraint.
--
-- Since 'Logical' includes a type family definition, using this function
-- requires enabling the @TypeFamilies@ extension.
--
-- Consider the following declarations:
--
-- > data Tree a
-- >   = Empty
-- >   | Leaf a
-- >   | Tree a :* Tree a
-- >   deriving (Generic)
-- > makeLogicType ''Tree
-- > deriving instance Generic (LogicTree a)
--
-- @makeLogicalInstance ''Tree ''LogicTree@ yields
--
-- > instance Logical a => Logical (Tree a) where
-- >   type Logic (Tree a) = LogicTree a
-- >   unify = genericUnify
-- >   walk = genericWalk
-- >   occursCheck = genericOccursCheck
-- >   inject = genericInject
-- >   extract = genericExtract
makeLogicalInstance :: Name -> Name -> Q [Dec]
makeLogicalInstance name logicTypeName = do
  TyConI declaration <- reify name
  variables <- case declaration of
    DataD _ _ variables _ _ _ -> return variables
    NewtypeD _ _ variables _ _ _ -> return variables
    other -> fail ("Expected a `data` or `newtype` declaration, but got:\n" <> show other)
  let constraints = logicalConstraints variables
  let typ = applyVariables name variables
  let logicTyp = applyVariables logicTypeName variables

  logicTypeFamily <- [d|type instance Logic $(return typ) = $(return logicTyp)|]
  let methods =
        [ method 'unify 'genericUnify
        , method 'walk 'genericWalk
        , method 'occursCheck 'genericOccursCheck
        , method 'inject 'genericInject
        , method 'extract 'genericExtract
        ]
  let body = logicTypeFamily <> methods
  let instanc = InstanceD Nothing constraints (AppT (ConT ''Logical) typ) body
  return [instanc]

-- | Generate 'Logical' instances, given pairs of a type and its logical
-- representation. This works like 'makeLogicalInstance', but better suits
-- mutually recursive types.
makeLogicalInstances :: [(Name, Name)] -> Q [Dec]
makeLogicalInstances = foldMap (uncurry makeLogicalInstance)

method :: Name -> Name -> Dec
method name generic = FunD name [Clause [] (NormalB (VarE generic)) []]

logicalConstraints :: [TyVarBndr flag] -> Cxt
logicalConstraints = map logicalConstraint

logicalConstraint :: TyVarBndr flag -> Pred
logicalConstraint variable = AppT (ConT ''Logical) (variableName variable)

variableName :: TyVarBndr flag -> Type
variableName (PlainTV name _) = VarT name
variableName (KindedTV name _ _) = VarT name

applyVariables :: Name -> [TyVarBndr flag] -> Type
applyVariables = foldl' (\typ -> AppT typ . variableName) . ConT
