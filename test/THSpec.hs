{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module THSpec (spec) where

import Data.Maybe (isJust, isNothing)
import GHC.Generics (Generic)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (arbitrary), frequency, label)

import Core
import LogicalBase ()
import TH

data Constructors
  = Simple
  | WithData Int
  | Char :@ Bool
  deriving (Eq, Show, Generic)

data Record a = Record
  { spam :: String
  , ham :: a
  }
  deriving (Generic)

data GADTLike where
  GADTLike :: Int -> GADTLike
  deriving (Generic)

data RecordGADTLike a where
  RecordGADTLike :: {gadtSpam :: a} -> RecordGADTLike a
  deriving (Generic)

newtype Newtype a = Newtype {runNewtype :: (a, a)} deriving (Generic)

makeLogic ''Constructors
makeLogic ''Record
makeLogic ''GADTLike
makeLogic ''RecordGADTLike
makeLogic ''Newtype

instance Arbitrary Constructors where
  arbitrary =
    frequency
      [ (1, pure Simple)
      , (20, WithData <$> arbitrary)
      , (30, (:@) <$> arbitrary <*> arbitrary)
      ]

ofTypeTerm :: Term a -> ()
ofTypeTerm = const ()

toConstr :: Constructors -> String
toConstr Simple = "Simple"
toConstr (WithData _) = "WithData"
toConstr (_ :@ _) = ":@"

spec :: Spec
spec = do
  describe "makeLogic" $ do
    it "generates proper constructors" $ do
      let _c LogicSimple = ()
          _c (LogicWithData x) = ofTypeTerm x
          _c (x :?@ y) = ofTypeTerm x `seq` ofTypeTerm y
      let _r LogicRecord{logicSpam = x, logicHam = y} =
            ofTypeTerm x `seq` ofTypeTerm y
      let _g (LogicGADTLike x) = ofTypeTerm x
      let _h LogicRecordGADTLike{logicGadtSpam = x} = ofTypeTerm x
      let _n LogicNewtype{logicRunNewtype = x} = ofTypeTerm x

      return @IO ()

    prop "generates proper inject and extract" $
      \(x :: Constructors) ->
        label (toConstr x) $
          extract (inject x) == Just x

    prop "generated extract returns Nothing for partial values" $ do
      let (_, var) = makeVariable empty

      extract (LogicWithData var) `shouldSatisfy` isNothing
      extract (var :?@ Value True) `shouldSatisfy` isNothing

    prop "generates proper unify" $
      \(x :: Constructors) ->
        label (toConstr x) $
          unify (inject x) (inject x) empty `shouldSatisfy` isJust
