{-# LANGUAGE TemplateHaskell #-}

module DeriveLogic (deriveLogic) where

import GHC.Generics (Generic)
import Language.Haskell.TH

import Core
import GenericUnifiable

deriveLogic :: Name -> Q [Dec]
deriveLogic ty = do
  TyConI dec <- reify ty
  logifyDec dec

logifyDec :: Dec -> Q [Dec]
logifyDec (DataD ctx name tyVars kind constructors _deriv) = do
  constructors' <- mapM logifyConstructor constructors
  let
    typeDefinition = DataD ctx name' tyVars kind constructors' derives
    name' = mkName ("Logic" ++ nameBase name)
    derives = [DerivClause Nothing [ConT ''Generic]]
  instances <- genInstance name tyVars name'
  return (typeDefinition : instances)

logifyDec FunD{} = fail "Cannot derive logic instances for a function!"
logifyDec ValD{} = fail "Cannot derive logic instances for a value!"
logifyDec NewtypeD{} = fail "Deriving logic instances for newtypes is not implemented yet!"
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
    name' = mkName ("Logic" ++ nameBase name)
    types' = map logifyBangType types
logifyConstructor RecC{} = fail "Deriving logic instances for record constructors is not implemented yet!"
logifyConstructor InfixC{} = fail "Deriving logic instances for infix constructors is not implemented yet!"
logifyConstructor ForallC{} = fail "Deriving logic instances for existential constructors is not implemented yet!"
logifyConstructor GadtC{} = fail "Deriving logic instances for GADT constructors is not implemented yet!"
logifyConstructor RecGadtC{} = fail "Deriving logic instances for record GADT constructors is not implemented yet!"

logifyBangType :: BangType -> BangType
logifyBangType = fmap logifyType

logifyType :: Type -> Type
logifyType = AppT (ConT ''ValueOrVar)

genInstance :: Name -> [TyVarBndr ()] -> Name -> Q [Dec]
genInstance name _vars name' = do
  let ctx = return (TupleT 0)
      name_ = return (ConT name)
      name'_ = return (ConT name')
  [d| instance $ctx => Unifiable $name_ where
        type Term $name_ = $name'_
        subst = genericSubst
        unify = genericUnify
        inject = genericInject
        extract = genericExtract
     |]
