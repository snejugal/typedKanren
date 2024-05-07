{-# LANGUAGE TemplateHaskell #-}

module DeriveLogic (deriveLogic) where

import Data.Char (toUpper)
import GHC.Generics (Generic)
import Language.Haskell.TH hiding (bang, cxt)

import Core
import Data.Foldable (foldl')
import GenericLogical

deriveLogic :: Name -> Q [Dec]
deriveLogic ty = do
  TyConI dec <- reify ty
  logifyDec dec

logifyDec :: Dec -> Q [Dec]
logifyDec (DataD ctx name tyVars kind constructors _deriv) = do
  constructors' <- mapM logifyConstructor constructors
  let
    typeDefinition = DataD ctx name' tyVars kind constructors' derives
    name' = logifyName name
    derives = [DerivClause Nothing [ConT ''Generic]]
  instances <- genInstance name tyVars name'
  return (typeDefinition : instances)
logifyDec (NewtypeD ctx name tyVars kind constructor _deriv) = do
  constructor' <- logifyConstructor constructor
  let
    typeDefinition = NewtypeD ctx name' tyVars kind constructor' derives
    name' = logifyName name
    derives = [DerivClause Nothing [ConT ''Generic]]
  instances <- genInstance name tyVars name'
  return (typeDefinition : instances)
logifyDec FunD{} = fail "Cannot derive logic instances for a function!"
logifyDec ValD{} = fail "Cannot derive logic instances for a value!"
logifyDec TySynD{} = fail "Cannot derive logic instances for type synonyms!"
logifyDec ClassD{} = fail "Cannot derive logic instances for type classes!"
logifyDec InstanceD{} = fail "Cannot derive logic instances for type class instances!"
logifyDec SigD{} = fail "Cannot derive logic instances for a type signature!"
logifyDec KiSigD{} = fail "Cannot derive logic instances for a kind signature!"
logifyDec ForeignD{} = fail "Cannot derive logic instances for a foreign function!"
logifyDec InfixD{} = fail "Cannot derive logic instances for a fixity declaration!"
logifyDec PragmaD{} = fail "Cannot derive logic instances for a pragma declaration!"
logifyDec DataFamilyD{} = fail "Cannot derive logic instances for a data family!"
logifyDec DataInstD{} = fail "Cannot derive logic instances for a data family instance!"
logifyDec NewtypeInstD{} = fail "Cannot derive logic instances for a data family instance!"
logifyDec TySynInstD{} = fail "Cannot derive logic instances for a type family instance!"
logifyDec OpenTypeFamilyD{} = fail "Cannot derive logic instances for a type family!"
logifyDec ClosedTypeFamilyD{} = fail "Cannot derive logic instances for a type family!"
logifyDec RoleAnnotD{} = fail "Cannot derive logic instances for a role annotation!"
logifyDec StandaloneDerivD{} = fail "Cannot derive logic instances for a standalone deriving!"
logifyDec DefaultSigD{} = fail "Cannot derive logic instances for a type signature!"
logifyDec PatSynD{} = fail "Deriving logic instances for pattern synonyms is not implemented yet!"
logifyDec PatSynSigD{} = fail "Cannot derive logic instances for a pattern synonym signature!"
logifyDec ImplicitParamBindD{} = fail "Cannot derive logic instances for an implicit param binding!"

logifyConstructor :: Con -> Q Con
logifyConstructor (NormalC name types) = return (NormalC name' types')
 where
  name' = logifyName name
  types' = map logifyBangType types
logifyConstructor (RecC name fields) = return (RecC name' fields')
 where
  name' = logifyName name
  fields' = map logifyField fields
logifyConstructor (InfixC left name right) = return (InfixC left' name' right')
 where
  left' = logifyBangType left
  right' = logifyBangType right
  name' = mkName (":?" ++ tail (nameBase name))
logifyConstructor (ForallC vars cxt inner) = ForallC vars cxt <$> logifyConstructor inner
logifyConstructor (GadtC names types ty) = do
  let names' = map logifyName names
  let types' = map logifyBangType types
  ty' <- logifyGadt ty
  return (GadtC names' types' ty')
logifyConstructor (RecGadtC names fields ty) = do
  let names' = map logifyName names
  let fields' = map logifyField fields
  ty' <- logifyGadt ty
  return (RecGadtC names' fields' ty')

logifyName :: Name -> Name
logifyName name = mkName ("Logic" ++ nameBase name)

logifyField :: VarBangType -> VarBangType
logifyField (name, bang, ty) = (name', bang, ty')
 where
  firstLetter : nameRest = nameBase name
  name' = mkName ("logic" ++ toUpper firstLetter : nameRest)
  ty' = logifyType ty

logifyBangType :: BangType -> BangType
logifyBangType = fmap logifyType

logifyType :: Type -> Type
logifyType = AppT (ConT ''ValueOrVar)

logifyGadt :: Type -> Q Type
logifyGadt (AppT left right) = do
  left' <- logifyGadt left
  return (AppT left' right)
logifyGadt (AppKindT inner kind) = do
  inner' <- logifyGadt inner
  return (AppKindT inner' kind)
logifyGadt (SigT inner kind) = do
  inner' <- logifyGadt inner
  return (SigT inner' kind)
logifyGadt (ConT name) = return (ConT (logifyName name))
logifyGadt ty = fail ("Found something complicated in GADT constructor's return type: " ++ show ty)

genInstance :: Name -> [TyVarBndr ()] -> Name -> Q [Dec]
genInstance name vars name' = do
  let ctx = return (genConstraints vars)
      name_ = return (applyVars name vars)
      name'_ = return (applyVars name' vars)
  [d|
    instance ($ctx) => Logical $name_ where
      type Term $name_ = $name'_
      subst = genericSubst
      unify = genericUnify
      inject = genericInject
      extract = genericExtract
    |]

genConstraints :: [TyVarBndr ()] -> Type
genConstraints vars = foldl' AppT tuple constraints
 where
  tuple = TupleT (length vars)
  constraints = map (AppT (ConT ''Logical) . VarT . extractVar) vars

applyVars :: Name -> [TyVarBndr flag] -> Type
applyVars name vars = foldl' AppT (ConT name) (map (VarT . extractVar) vars)

extractVar :: TyVarBndr flag -> Name
extractVar (PlainTV v _) = v
extractVar (KindedTV v _ _) = v
