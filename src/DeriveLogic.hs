{-# LANGUAGE TemplateHaskell #-}

module DeriveLogic (deriveLogic) where

import GHC.Generics (Generic)
import Language.Haskell.TH

deriveLogic :: Name -> Q [Dec]
deriveLogic ty = do
  TyConI dec <- reify ty
  logifyDec dec

logifyDec :: Dec -> Q [Dec]
logifyDec (DataD ctx name tyVars kind constructors []) = return [typeDefinition]
  where
    typeDefinition = DataD ctx name' tyVars kind constructors' derives
    name' = mkName ("Logic" ++ nameBase name)
    constructors' = map logifyConstructor constructors
    derives = [DerivClause Nothing [ConT ''Generic]]

logifyConstructor :: Con -> Con
logifyConstructor (NormalC name types) = NormalC name' types'
  where
    name' = mkName ("Logic" ++ nameBase name)
    types' = map logifyBangType types

logifyBangType :: BangType -> BangType
logifyBangType = fmap logifyType

logifyType :: Type -> Type
logifyType = AppT (ConT (mkName "Lib.ValueOrVar")) -- todo: ''ValueOrVar?
