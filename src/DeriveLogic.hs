{-# LANGUAGE TemplateHaskell #-}

module DeriveLogic (deriveLogic) where

import GHC.Generics (Generic)
import Language.Haskell.TH

deriveLogic :: Name -> Q [Dec]
deriveLogic ty = do
  TyConI dec <- reify ty
  logifyDec dec

logifyDec :: Dec -> Q [Dec]
logifyDec (DataD ctx name tyVars kind constructors []) = return [typeDefinition, instanceDef]
  where
    typeDefinition = DataD ctx name' tyVars kind constructors' derives
    name' = mkName ("Logic" ++ nameBase name)
    constructors' = map logifyConstructor constructors
    derives = [DerivClause Nothing [ConT ''Generic]]

    instanceDef = genInstance name tyVars name'

logifyConstructor :: Con -> Con
logifyConstructor (NormalC name types) = NormalC name' types'
  where
    name' = mkName ("Logic" ++ nameBase name)
    types' = map logifyBangType types

logifyBangType :: BangType -> BangType
logifyBangType = fmap logifyType

logifyType :: Type -> Type
logifyType = AppT (ConT (mkName "Lib.ValueOrVar")) -- todo: ''ValueOrVar?

genInstance :: Name -> [TyVarBndr ()] -> Name -> Dec
genInstance name _vars name' = InstanceD Nothing ctx instanceTy decs
  where
    -- todo: include variables
    ctx = []
    instanceTy = AppT (ConT (mkName "Lib.Unifiable")) (ConT name)

    decs = [
      TySynInstD (TySynEqn Nothing (AppT (ConT (mkName "Term")) (ConT name)) (ConT name')),
      FunD (mkName "subst") [Clause [] (NormalB (VarE (mkName "Lib.genericSubst"))) []],
      FunD (mkName "unify") [Clause [] (NormalB (VarE (mkName "Lib.genericUnify"))) []],
      FunD (mkName "inject") [Clause [] (NormalB (VarE (mkName "Lib.genericInject"))) []],
      FunD (mkName "extract") [Clause [] (NormalB (VarE (mkName "Lib.genericExtract"))) []]]
