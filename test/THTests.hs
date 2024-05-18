{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module THTests (runTests) where

import Data.Maybe (isNothing)
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (arbitrary), oneof, quickCheckAll)

import Core
import LogicalBase ()
import TH

data OneOf
  = Number Int
  | String String
  deriving (Eq, Show, Generic)

instance Arbitrary OneOf where
  arbitrary = oneof [Number <$> arbitrary, String <$> arbitrary]

makeLogic ''OneOf
deriving instance (Eq LogicOneOf)

ofTypeTerm :: Term a -> ()
ofTypeTerm = const ()

_logicOneOfConstructors :: LogicOneOf -> ()
_logicOneOfConstructors (LogicNumber x) = ofTypeTerm x
_logicOneOfConstructors (LogicString x) = ofTypeTerm x

prop_transform :: OneOf -> Bool
prop_transform x = extract (inject x) == Just x

prop_extractVar :: Bool
prop_extractVar = isNothing (extract (LogicNumber var))
 where
  (_, var) = makeVariable empty

data Pair a b = a :* b deriving (Generic)

makeLogic ''Pair

_logicPairConstructors :: LogicPair a b -> ()
_logicPairConstructors (x :?* y) = ofTypeTerm x `seq` ofTypeTerm y

data Person = Person {name :: String, age :: Int} deriving (Generic)

makeLogic ''Person

_logicPersonConstructors :: LogicPerson -> ()
_logicPersonConstructors LogicPerson{logicName = x, logicAge = y} =
  ofTypeTerm x `seq` ofTypeTerm y

data AlmostGadt a where
  AlmostGadt :: a -> AlmostGadt a
  deriving (Generic)

makeLogic ''AlmostGadt

_almostGadtConstructors :: LogicAlmostGadt a -> ()
_almostGadtConstructors (LogicAlmostGadt x) = ofTypeTerm x

data Person' where
  Person' :: {name' :: String, age' :: Int} -> Person'
  deriving (Generic)

makeLogic ''Person'

_logicPerson'Constructors :: LogicPerson' -> ()
_logicPerson'Constructors LogicPerson'{logicName' = x, logicAge' = y} =
  ofTypeTerm x `seq` ofTypeTerm y

newtype Newbool = Newbool {runNewbool :: Bool} deriving (Generic)

makeLogic ''Newbool

_logicNewboolConstructors :: LogicNewbool -> ()
_logicNewboolConstructors LogicNewbool{logicRunNewbool = x} = ofTypeTerm x

return []
runTests :: IO Bool
runTests = $quickCheckAll
