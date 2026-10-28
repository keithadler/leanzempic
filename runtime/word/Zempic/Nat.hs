-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- FAST MODE: Lean Nat as Word (64-bit). Arithmetic that would exceed 2^64 - 1
-- aborts with an error instead of wrapping, so wrong answers cannot happen
-- silently. Use only for programs whose numbers stay below 2^64.
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Zempic.Nat where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import GHC.Exts
import GHC.Word (Word(W#))

type ZNat = Word

overflow :: a
overflow = error "leanzempic: Nat overflow (word mode: value exceeds 2^64-1)"
{-# NOINLINE overflow #-}

natZero :: ZNat
natZero = 0

natAdd, natSub, natMul, natDiv, natMod, natPow, natShr, natShl, natAnd, natOr, natXor, natGcd
  :: ZNat -> ZNat -> ZNat
natAdd (W# a) (W# b) = case addWordC# a b of (# r, 0# #) -> W# r; _ -> overflow
natSub x y = if x >= y then x - y else 0
natMul (W# a) (W# b) = case timesWord2# a b of (# 0##, lo #) -> W# lo; _ -> overflow
natDiv x y = if y == 0 then 0 else quot x y
natMod x y = if y == 0 then x else rem x y
natPow x y = go 1 y
  where go !acc 0 = acc
        go !acc n = go (natMul acc x) (n - 1)
natShr x y = if y >= 64 then 0 else shiftR x (fromIntegral y)
natShl x y
  | x == 0 = 0
  | y >= 64 || shiftR (shiftL x (fromIntegral y)) (fromIntegral y) /= x = overflow
  | otherwise = shiftL x (fromIntegral y)
natAnd = (.&.)
natOr = (.|.)
natXor = xor
natGcd = gcd

natEq, natLt, natLe :: ZNat -> ZNat -> Bool
natEq = (==)
natLt = (<)
natLe = (<=)

natSucc :: ZNat -> ZNat
natSucc x = natAdd x 1

{-# INLINE natAdd #-}
{-# INLINE natSub #-}
{-# INLINE natMul #-}
{-# INLINE natDiv #-}
{-# INLINE natMod #-}
{-# INLINE natShr #-}
{-# INLINE natEq #-}
{-# INLINE natLt #-}
{-# INLINE natLe #-}
{-# INLINE natSucc #-}
