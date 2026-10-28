-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Exact Lean Nat as Haskell Natural (arbitrary precision).
module Zempic.Nat.Exact where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import GHC.Exts (build)
import Numeric.Natural (Natural)
import Data.List (foldl')
import Zempic.Runtime (Any, zo, zu)

type ZNat = Natural

natZero :: ZNat
natZero = 0

natAdd, natSub, natMul, natDiv, natMod, natPow, natShr, natShl, natAnd, natOr, natXor, natGcd
  :: ZNat -> ZNat -> ZNat
natAdd = (+)
natSub x y = if x >= y then x - y else 0
natMul = (*)
natDiv x y = if y == 0 then 0 else quot x y
natMod x y = if y == 0 then x else rem x y
natPow = (^)
natShr x y = shiftR x (fromIntegral y)
natShl x y = shiftL x (fromIntegral y)
natAnd = (.&.)
natOr = (.|.)
natXor = xor
natGcd = gcd

natEq, natLt, natLe :: ZNat -> ZNat -> Bool
natEq = (==)
natLt = (<)
natLe = (<=)

natSucc :: ZNat -> ZNat
natSucc = (+ 1)

{-# INLINE natAdd #-}
{-# INLINE natSub #-}
{-# INLINE natMul #-}
{-# INLINE natDiv #-}
{-# INLINE natMod #-}
{-# INLINE natPow #-}
{-# INLINE natShr #-}
{-# INLINE natShl #-}
{-# INLINE natAnd #-}
{-# INLINE natOr #-}
{-# INLINE natXor #-}
{-# INLINE natGcd #-}
{-# INLINE natEq #-}
{-# INLINE natLt #-}
{-# INLINE natLe #-}
{-# INLINE natSucc #-}

-- Explicit build so GHC's foldr/build fusion always sees the producer.
zRange :: ZNat -> [Any]
zRange n = map zo (build (\c nil ->
  let go i = if i >= n then nil else i `c` go (i + 1) in go 0))
{-# INLINE zRange #-}

zLength :: [Any] -> ZNat
zLength xs = fromIntegral (length xs)
{-# INLINE zLength #-}

zSum :: [Any] -> ZNat
zSum = foldl' (\a x -> natAdd a (zu x)) 0
{-# INLINE zSum #-}

zTake :: ZNat -> [Any] -> [Any]
zTake n = take (fromIntegral (min n 4611686018427387903))
{-# INLINE zTake #-}
