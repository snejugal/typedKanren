{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Binary (
  Bit (..),
  LogicBit (..),
  _LogicO,
  _LogicI,
  _LogicO',
  _LogicI',
  Binary,
  zeroo,
  poso,
  gtlo,
  binaryo,
  addo,
  subo,
  lesso,
  mulo,
  divo,
  example,
) where

import Control.Lens (Prism, from)
import Control.Lens.TH (makePrisms)
import Control.Monad (void)
import Data.Bifunctor (bimap)
import Data.Function ((&))
import Data.Tagged (Tagged)
import GHC.Generics (Generic)

import Core
import Goal
import LogicalBase
import Match
import TH

data Bit = O | I deriving (Eq, Show, Generic)

makeLogic ''Bit
deriving instance Show LogicBit

makePrisms ''LogicBit

_LogicO'
  :: Prism
      (Tagged (o, i) LogicBit)
      (Tagged (o', i) LogicBit)
      (Tagged o ())
      (Tagged o' ())
_LogicO' = from _Tagged . _LogicO . _Tagged

_LogicI'
  :: Prism
      (Tagged (o, i) LogicBit)
      (Tagged (o, i') LogicBit)
      (Tagged i ())
      (Tagged i' ())
_LogicI' = from _Tagged . _LogicI . _Tagged

type Binary = [Bit]

instance Num Binary where
  fromInteger 0 = []
  fromInteger 1 = [I]
  fromInteger x | x > 1 = bit : fromInteger (x `div` 2)
   where
    bit
      | even x = O
      | otherwise = I
  fromInteger _ = error "Binary numbers cannot be negative"

  (+) = undefined
  (*) = undefined
  abs = id
  signum = undefined
  negate = undefined

zeroo :: Term Binary -> Goal ()
zeroo n = n === Value LogicNil

cons :: (Logical a) => Term [a] -> Goal (Term a, Term [a])
cons list = do
  (x, xs) <- fresh
  list === Value (LogicCons x xs)
  return (x, xs)

poso :: Term Binary -> Goal ()
poso = void . cons

gtlo :: Term Binary -> Goal ()
gtlo n = do
  (_, ns) <- cons n
  poso ns

{- FOURMOLU_DISABLE -}
binaryo :: Term Binary -> Goal ()
binaryo = matche'
  & on' _LogicNil' return
  & on' _LogicCons' (\(b, bs) -> do
      b & (matche'
        & on' _LogicI' return
        & on' _LogicO' (\() -> poso bs)
        & enter')
      binaryo bs)
  & enter'

lesslo :: (Logical a, Logical b) => Term [a] -> Term [b] -> Goal ()
lesslo xs ys = do
  (y, ys') <- fresh
  ys === Value (LogicCons y ys')
  xs & (matche'
    & on' _LogicNil' return
    & on' _LogicCons' (\(_, xs') -> lesslo xs' ys')
    & enter')

samelo :: (Logical a, Logical b) => Term [a] -> Term [b] -> Goal ()
samelo xs = matche'
  & on' _LogicNil' (\() -> xs === inject' [])
  & on' _LogicCons' (\(_, ys') -> do
      (_, xs') <- cons xs
      samelo xs' ys')
  & enter'

lessl3o
  :: (Logical a, Logical b, Logical c, Logical d)
  => Term [a]
  -> Term [b]
  -> Term [c]
  -> Term [d]
  -> Goal ()
lessl3o a x y z = a & (matche'
  & on' _LogicNil' (\() -> void (cons x))
  & on' _LogicCons' (\(_, ar) -> do
      (_, xr) <- cons x
      y & (matche'
        & on' _LogicNil' (\() -> do
            (_, zr) <- cons z
            lessl3o ar xr y zr)
        & on' _LogicCons' (\(_, yr) -> lessl3o ar xr yr z)
        & enter'))
  & enter')
{- FOURMOLU_ENABLE -}

toBit :: Term Bit -> Goal Bit
toBit =
  matche'
    & on' _LogicO' (\() -> return O)
    & on' _LogicI' (\() -> return I)
    & enter'

full1Addero :: Term Bit -> Term Bit -> Term Bit -> Term Bit -> Term Bit -> Goal ()
full1Addero carryIn a b s carryOut = do
  sumOfBits <- (fmap (length . filter (== I)) . mapM toBit) [carryIn, a, b]
  case sumOfBits of
    0 -> (carryOut === inject' O) `conj` (s === inject' O)
    1 -> (carryOut === inject' O) `conj` (s === inject' I)
    2 -> (carryOut === inject' I) `conj` (s === inject' O)
    3 -> (carryOut === inject' I) `conj` (s === inject' I)
    _ -> failo

fullNAddero :: Term Bit -> Term Binary -> Term Binary -> Term Binary -> Goal ()
fullNAddero carryIn a b r =
  disjMany
    [ do
        zeroo b
        carryIn
          & ( matche'
                & on' _LogicO' (\() -> a === r)
                & on' _LogicI' (\() -> fullNAddero (inject' O) a (inject' [I]) r)
                & enter'
            )
    , do
        zeroo a
        poso b
        fullNAddero carryIn b a r
    , do
        a === inject' [I]
        b === inject' [I]
        (r1, r2) <- fresh
        r === Value (LogicCons r1 (Value (LogicCons r2 (Value LogicNil))))
        full1Addero carryIn (inject' I) (inject' I) r1 r2
    , do
        a === inject' [I]
        (bb, br) <- cons b
        poso br
        (rb, rr) <- cons r
        poso rr

        carryOut <- fresh
        full1Addero carryIn (inject' I) bb rb carryOut
        fullNAddero carryOut (inject' []) br rr
    , do
        b === inject' [I]
        gtlo a
        gtlo r
        fullNAddero carryIn b a r
    , do
        (ab, ar) <- cons a
        poso ar
        (bb, br) <- cons b
        poso br
        (rb, rr) <- cons r
        poso rr

        carryOut <- fresh
        full1Addero carryIn ab bb rb carryOut
        fullNAddero carryOut ar br rr
    ]

addo :: Term Binary -> Term Binary -> Term Binary -> Goal ()
addo = fullNAddero (inject' O)

subo :: Term Binary -> Term Binary -> Term Binary -> Goal ()
subo a b c = addo b c a

lesso :: Term Binary -> Term Binary -> Goal ()
lesso a b = do
  x <- fresh
  poso x
  addo a x b

mulo :: Term Binary -> Term Binary -> Term Binary -> Goal ()
mulo a b c =
  disjMany
    [ do
        a === inject' []
        c === a
    , do
        b === inject' []
        c === b
        poso a
    , do
        a === inject' [I]
        b === c
    , do
        (ar, cr) <- fresh
        a === Value (LogicCons (inject' O) ar)
        c === Value (LogicCons (inject' O) cr)
        poso b
        poso ar
        poso cr
        mulo ar b cr
    , do
        ar <- fresh
        a === Value (LogicCons (inject' I) ar)
        poso b
        poso ar
        gtlo c

        c1 <- fresh
        lessl3o c1 c a b

        mulo ar b c1
        addo (Value (LogicCons (inject' O) c1)) b c
    ]

{- FOURMOLU_DISABLE -}
divo :: Term Binary -> Term Binary -> Term Binary -> Term Binary -> Goal ()
divo n m q r =
  disjMany
    [ do
        q === inject' []
        n === r
        lesso n m
    , do
        q === inject' [I]
        samelo n m
        binaryo n
        addo r m n
        lesso r m
    , do
        lesslo m n
        lesso r m
        poso q

        (n1, n2) <- fresh
        splito n r n1 n2
        (q1, q2) <- fresh
        splito q r q1 q2
        q2m <- fresh
        n1 & (matche'
          & on' _LogicNil' (\() -> do
              q1 === inject' []
              subo n2 r q2m
              mulo q2 m q2m)
          & on' _LogicCons' (\_ -> do
              (q2mr, rr, r1) <- fresh
              mulo q2 m q2m
              addo q2m r q2mr
              subo q2mr n2 rr
              splito rr r r1 (inject' [])
              divo n1 m q1 r1)
          & enter')
    ]
{- FOURMOLU_ENABLE -}

splito :: Term Binary -> Term Binary -> Term Binary -> Term Binary -> Goal ()
splito n r n1 n2 =
  disjMany
    [ do
        n === inject' []
        n1 === inject' []
        n2 === inject' []
    , do
        (b, n') <- cons n
        b === inject' O
        poso n'

        r === inject' []
        n1 === n'
        n2 === inject' []
    , do
        (b, n') <- cons n
        b === inject' I

        r === inject' []
        n1 === n'
        n2 === inject' [I]
    , do
        (b, n') <- cons n
        b === inject' O
        poso n'

        (_, r') <- cons r
        n2 === inject' []
        splito n' r' n1 n2
    , do
        (b, n') <- cons n
        b === inject' I

        (_, r') <- cons r
        n2 === inject' [I]
        splito n' r' n1 (inject' [])
    , do
        (b, n') <- cons n
        (_, r') <- cons r

        n2' <- fresh
        poso n2'
        n2 === Value (LogicCons b n2')
        splito n' r' n1 n2'
    ]

trimap :: (a -> b) -> (a, a, a) -> (b, b, b)
trimap f (x, y, z) = (f x, f y, f z)

quadmap :: (a -> b) -> (a, a, a, a) -> (b, b, b, b)
quadmap f (x, y, z, w) = (f x, f y, f z, f w)

tryExtract' :: (Logical a) => Term a -> Either (Term a) a
tryExtract' x = maybe (Left x) Right (extract' x)

example :: IO ()
example = do
  putStrLn "addo 3 5 x:"
  mapM_ print $ extract' <$> run (addo (inject' 3) (inject' 5))
  putStrLn "\naddo 2 x 8:"
  mapM_ print $ extract' <$> run (\x -> addo (inject' 2) x (inject' 8))
  putStrLn "\naddo 8 x 2:"
  print $ extract' <$> run (\x -> addo (inject' 8) x (inject' 2))
  putStrLn "\naddo x y 8:"
  mapM_ print $ bimap extract' extract' <$> run (\(x, y) -> addo x y (inject' 8))
  putStrLn "\naddo x y z:"
  mapM_ print $ take 10 $ trimap tryExtract' <$> run (\(x, y, z) -> addo x y z)

  putStrLn "\nmulo 3 4 x:"
  mapM_ print $ extract' <$> run (mulo (inject' 3) (inject' 4))
  putStrLn "\nmulo 2 x 12:"
  mapM_ print $ extract' <$> run (\x -> mulo (inject' 2) x (inject' 12))
  putStrLn "\nmulo 12 x 2:"
  print $ extract' <$> run (\x -> mulo (inject' 12) x (inject' 2))
  putStrLn "\nmulo x y 12:"
  mapM_ print $ bimap extract' extract' <$> run (\(x, y) -> mulo x y (inject' 12))
  putStrLn "\nmulo x y z:"
  mapM_ print $ take 10 $ trimap tryExtract' <$> run (\(x, y, z) -> mulo x y z)

  putStrLn "\ndivo 15 4 q r:"
  mapM_ print $ bimap extract' extract' <$> run (uncurry (divo (inject' 15) (inject' 4)))
  putStrLn "\ndivo n 3 2 1:"
  mapM_ print $ extract' <$> run (\n -> divo n (inject' 3) (inject' 2) (inject' 1))
  putStrLn "\ndivo 13 m 2 1:"
  mapM_ print $ extract' <$> run (\m -> divo (inject' 13) m (inject' 2) (inject' 1))
  putStrLn "\ndivo n m q r:"
  mapM_ print $ take 10 $ quadmap tryExtract' <$> run (\(n, m, q, r) -> divo n m q r)
