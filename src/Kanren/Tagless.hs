{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash    #-}
-- | "Tagless" sum types allow to skip explicit tag for at least one of the alternatives in a sum type,
-- assuming that we can differentiate between the alternatives at runtime by other means.
--
-- The benefit of this representation is pronounced for recursive data types:
--
-- * In the fastest miniKanren implementations, this approach is used
--   to avoid expensive recursive injection of a regular (non-logical) value into a miniKanren program.
--   See Section 6 of [1] for more details about typed implementation of tagless approach in OCanren.
--   Note that faster-minikanren implementation (in Scheme/Racket) is also using a similar technique in an untyped setting.
--
-- * An efficient bignum representation can be done by "unboxing" the (small) integer constructor.
--   See the details of this example in [2].
--
-- This "tagless" representation approach is a variation of
-- * niche filling optimization [3] (which can be found in Rust, for instance)
-- * unboxed constructors [2]
--
-- See also "flat Maybe" implementation by Andras Kovacs: <https://github.com/AndrasKovacs/flat-maybe>
--
-- Note that this approach is NOT the same as unboxed sum typed in Haskell (at least not in their current form).
--
-- [1] Dmitrii Kosarev, Dmitry Boulytchev. Typed Embedding of a Relational Language in OCaml <https://arxiv.org/abs/1805.11006>
-- [2] Nicolas Chataing, Stephen Dolan, Gabriel Scherer, and Jeremy Yallop. 2024. Unboxed Data Constructors: Or, How cpp Decides a Halting Problem. Proc. ACM Program. Lang. 8, POPL, Article 51 (January 2024), 31 pages. https://doi.org/10.1145/3632893
-- [3] Bartell-Mangel, N. L. (2022). Filling a Niche: Using Spare Bits to Optimize Data Representations.
module Kanren.Tagless where

import           Control.DeepSeq   (NFData (rnf))
import qualified Foreign.Ptr       as Foreign
import qualified Foreign.StablePtr as Foreign
import           GHC.Exts          (Int (I#), closureSize#)
import           System.IO.Unsafe  (unsafePerformIO)
import           Unsafe.Coerce     (unsafeCoerce)

-- | A value of type 'Anchor' is used
-- as a runtime tag for the extra data in the 'Tagless' sum type.
type Anchor = Int

-- | The anchor
theAnchor :: Anchor
{-# NOINLINE theAnchor #-}
theAnchor = unsafePerformIO $ do
  sptr <- Foreign.newStablePtr theAnchor
  let ptr = Foreign.castStablePtrToPtr sptr
      Foreign.IntPtr n = Foreign.ptrToIntPtr ptr
  return $! (n - 2837641298) -- scrambled integer value of a stable pointer to the anchor itself
                             -- the hope is that it is sufficiently unique and will not interfere with any user data

-- | Extra data packed with an 'Anchor' (a runtime tag, specifying that these are indeed extra data).
data Extra extra = Extra
  { _extraAnchor :: {-# UNPACK #-} !Anchor
  , _getExtra    :: !extra
  }

-- | Make a sum type, but do not use any runtime tag for @a@.
-- This effectively allows injecting (tagged) values of type @extra@
-- into the type of @a@, meaning that coercion from @a@ to @'Tagless' extra a@ is zero-cost.
newtype Tagless extra a = Tagless a

instance (Eq extra, Eq a) => Eq (Tagless extra a) where
  x == y = inspectTagless x == inspectTagless y

instance (NFData extra, NFData a) => NFData (Tagless extra a) where
  rnf x = case inspectTagless x of
    Left l  -> rnf l
    Right r -> rnf r

-- | Returns the size of the given closure in machine words.
--
-- A wrapper around 'closureSize#'.
--
-- Note that in many situations it will return the size of a thunk.
-- This might be especially surprising/inconsistent when dealing with polymorphic constants:
--
-- >>> closureSize ([] :: [Int])
-- 4
-- >>> closureSize (Nothing :: Maybe Int)
-- 2
--
-- See 'closureSize'' for the stricter version.
closureSize :: a -> Int
closureSize x = I# (closureSize# x)

-- | A strict version of 'closureSize'.
--
-- >>> closureSize' ([] :: [Int])
-- 2
-- >>> closureSize' (Nothing :: Maybe Int)
-- 2
-- >>> closureSize' ()
-- 2
-- >>> closureSize' (extra False :: Tagless Bool [Int])
-- 3
-- >>> closureSize' (tagless [1,2,3] :: Tagless Bool [Int])
-- 3
-- >>> closureSize' (tagless [] :: Tagless Bool [Int])
-- 2
closureSize' :: a -> Int
closureSize' !x = closureSize x

-- | Inspect a value of type @a@ to see if it contains @extra@ data
-- via 'Tagless' representation.
inspectAsTagless :: a -> Either extra a
{-# INLINE inspectAsTagless #-}
inspectAsTagless = inspectTagless . tagless

-- | Check if a given 'Tagless' sum type is @extra@ or not.
--
-- >>> inspectTagless (extra 123 :: Tagless Int [Int])
-- Left 123
-- >>> inspectTagless (tagless [] :: Tagless Int [Int])
-- Right []
-- >>> inspectTagless (tagless [123] :: Tagless Int [Int])
-- Right [123]
inspectTagless :: Tagless extra a -> Either extra a
{-# NOINLINE inspectTagless #-}
inspectTagless (Tagless !x)
  | closureSize x < 3 = Right x
  | otherwise =
      case unsafeCoerce x of
        Extra anchor extra_ | anchor == theAnchor ->
          Left extra_
        _ -> Right x

-- | Wrap a value into a 'Tagless' sum type.
-- This operation is zero-cost and amounts to a simple coercion.
tagless :: a -> Tagless extra a
tagless = Tagless

-- | Wrap @extra@ data into a 'Tagless' sum type.
-- This operation adds a runtime tag which is inspectable via 'inspectTagless'.
extra :: extra -> Tagless extra a
extra x = unsafeCoerce (Extra theAnchor x)

-- * Some simple examples/tests

test :: String -> [Either Int (Either Bool String)]
test s =
  [ inspectTagless (tagless (Right "Hello"))
  , inspectTagless (tagless (Left True))
  , inspectTagless (tagless (Left False))
  , inspectTagless (tagless (Right "world"))
  , inspectTagless (extra 1)
  , inspectTagless (extra 123)
  , inspectTagless (extra 0)
  , inspectTagless (tagless (Right s))
  , inspectTagless (tagless (Left (null s)))]

data Undefined = Undefined

taglessCaseList :: [a] -> (extra -> r) -> r -> ((a, Tagless extra [a]) -> r) -> r
taglessCaseList zs handleExtra handleEmpty handleNonEmpty =
  case inspectAsTagless zs of
    Left extra_  -> handleExtra extra_
    Right []     -> handleEmpty
    Right (x:xs) -> handleNonEmpty (x, tagless xs)

sampleList1 :: Tagless Undefined [Int]
sampleList1 = tagless [1..10]

cons :: a -> Tagless extra [a] -> Tagless extra [a]
cons x xs = tagless (x : unsafeCoerce xs)

sampleList2 :: Tagless Undefined [Int]
sampleList2 = 1 `cons` (2 `cons` extra Undefined)

ppListAsTagless :: Show a => [a] -> String
ppListAsTagless t =
  case inspectAsTagless t of
    Left _       -> "EXTRA"
    Right []     -> "END OF LIST"
    -- Right [x]    -> show x
    Right (x:xs) -> show x ++ ", " ++ ppListAsTagless xs
