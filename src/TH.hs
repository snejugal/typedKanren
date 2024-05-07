{-# LANGUAGE TemplateHaskell #-}

module TH (makeLogic) where

import Data.Char (toUpper)
import GHC.Generics (Generic)
import Language.Haskell.TH hiding (bang, cxt)

import Core
import Data.Foldable (foldl')
import GenericLogical

makeLogic :: Name -> Q [Dec]
makeLogic ty = do
  TyConI dec <- reify ty
  makeDecLogic dec

makeDecLogic :: Dec -> Q [Dec]
makeDecLogic (DataD ctx name tyVars kind constructors _deriv) = do
  constructors' <- mapM makeLogicCon constructors
  let
    typeDefinition = DataD ctx name' tyVars kind constructors' derives
    name' = makeLogicName name
    derives = [DerivClause Nothing [ConT ''Generic]]
  instances <- makeLogical name tyVars name'
  return (typeDefinition : instances)
makeDecLogic (NewtypeD ctx name tyVars kind constructor _deriv) = do
  constructor' <- makeLogicCon constructor
  let
    typeDefinition = NewtypeD ctx name' tyVars kind constructor' derives
    name' = makeLogicName name
    derives = [DerivClause Nothing [ConT ''Generic]]
  instances <- makeLogical name tyVars name'
  return (typeDefinition : instances)
makeDecLogic FunD{} = fail "Cannot derive logic instances for a function!"
makeDecLogic ValD{} = fail "Cannot derive logic instances for a value!"
makeDecLogic TySynD{} = fail "Cannot derive logic instances for type synonyms!"
makeDecLogic ClassD{} = fail "Cannot derive logic instances for type classes!"
makeDecLogic InstanceD{} = fail "Cannot derive logic instances for type class instances!"
makeDecLogic SigD{} = fail "Cannot derive logic instances for a type signature!"
makeDecLogic KiSigD{} = fail "Cannot derive logic instances for a kind signature!"
makeDecLogic ForeignD{} = fail "Cannot derive logic instances for a foreign function!"
makeDecLogic InfixD{} = fail "Cannot derive logic instances for a fixity declaration!"
makeDecLogic PragmaD{} = fail "Cannot derive logic instances for a pragma declaration!"
makeDecLogic DataFamilyD{} = fail "Cannot derive logic instances for a data family!"
makeDecLogic DataInstD{} = fail "Cannot derive logic instances for a data family instance!"
makeDecLogic NewtypeInstD{} = fail "Cannot derive logic instances for a data family instance!"
makeDecLogic TySynInstD{} = fail "Cannot derive logic instances for a type family instance!"
makeDecLogic OpenTypeFamilyD{} = fail "Cannot derive logic instances for a type family!"
makeDecLogic ClosedTypeFamilyD{} = fail "Cannot derive logic instances for a type family!"
makeDecLogic RoleAnnotD{} = fail "Cannot derive logic instances for a role annotation!"
makeDecLogic StandaloneDerivD{} = fail "Cannot derive logic instances for a standalone deriving!"
makeDecLogic DefaultSigD{} = fail "Cannot derive logic instances for a type signature!"
makeDecLogic PatSynD{} = fail "Deriving logic instances for pattern synonyms is not implemented yet!"
makeDecLogic PatSynSigD{} = fail "Cannot derive logic instances for a pattern synonym signature!"
makeDecLogic ImplicitParamBindD{} = fail "Cannot derive logic instances for an implicit param binding!"

makeLogicCon :: Con -> Q Con
makeLogicCon (NormalC name types) = return (NormalC name' types')
 where
  name' = makeLogicName name
  types' = map makeLogicBangType types
makeLogicCon (RecC name fields) = return (RecC name' fields')
 where
  name' = makeLogicName name
  fields' = map makeLogicField fields
makeLogicCon (InfixC left name right) = return (InfixC left' name' right')
 where
  left' = makeLogicBangType left
  right' = makeLogicBangType right
  name' = mkName (":?" ++ tail (nameBase name))
makeLogicCon (ForallC vars cxt inner) = ForallC vars cxt <$> makeLogicCon inner
makeLogicCon (GadtC names types ty) = do
  let names' = map makeLogicName names
  let types' = map makeLogicBangType types
  ty' <- makeLogicGadtReturnType ty
  return (GadtC names' types' ty')
makeLogicCon (RecGadtC names fields ty) = do
  let names' = map makeLogicName names
  let fields' = map makeLogicField fields
  ty' <- makeLogicGadtReturnType ty
  return (RecGadtC names' fields' ty')

makeLogicName :: Name -> Name
makeLogicName name = mkName ("Logic" ++ nameBase name)

makeLogicField :: VarBangType -> VarBangType
makeLogicField (name, bang, ty) = (name', bang, ty')
 where
  firstLetter : nameRest = nameBase name
  name' = mkName ("logic" ++ toUpper firstLetter : nameRest)
  ty' = makeLogicType ty

makeLogicBangType :: BangType -> BangType
makeLogicBangType = fmap makeLogicType

makeLogicType :: Type -> Type
makeLogicType = AppT (ConT ''Term)

makeLogicGadtReturnType :: Type -> Q Type
makeLogicGadtReturnType (AppT left right) = do
  left' <- makeLogicGadtReturnType left
  return (AppT left' right)
makeLogicGadtReturnType (AppKindT inner kind) = do
  inner' <- makeLogicGadtReturnType inner
  return (AppKindT inner' kind)
makeLogicGadtReturnType (SigT inner kind) = do
  inner' <- makeLogicGadtReturnType inner
  return (SigT inner' kind)
makeLogicGadtReturnType (ConT name) = return (ConT (makeLogicName name))
makeLogicGadtReturnType ty = fail ("Found something complicated in GADT constructor's return type: " ++ show ty)

makeLogical :: Name -> [TyVarBndr ()] -> Name -> Q [Dec]
makeLogical name vars name' = do
  let ctx = return (makeLogicalConstraints vars)
      name_ = return (applyVars name vars)
      name'_ = return (applyVars name' vars)
  [d|
    instance ($ctx) => Logical $name_ where
      type Logic $name_ = $name'_
      subst = genericSubst
      unify = genericUnify
      inject = genericInject
      extract = genericExtract
    |]

makeLogicalConstraints :: [TyVarBndr ()] -> Type
makeLogicalConstraints vars = foldl' AppT tuple constraints
 where
  tuple = TupleT (length vars)
  constraints = map (AppT (ConT ''Logical) . VarT . extractVar) vars

applyVars :: Name -> [TyVarBndr flag] -> Type
applyVars name vars = foldl' AppT (ConT name) (map (VarT . extractVar) vars)

extractVar :: TyVarBndr flag -> Name
extractVar (PlainTV v _) = v
extractVar (KindedTV v _ _) = v
