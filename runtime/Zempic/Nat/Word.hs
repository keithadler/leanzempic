-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- FAST PATH: Lean Nat as Word (64-bit). Arithmetic that would exceed 2^64 - 1
-- throws `ZOverflow` instead of wrapping, so a wrong answer cannot happen
-- silently. In auto mode the wrapper catches it and reruns with Zempic.Nat.Exact.
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Zempic.Nat.Word where

import Data.Word (Word16, Word32, Word64, Word8)
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Control.Exception (Exception (..), throw)
import GHC.Exts
import Data.List (foldl')
import Zempic.Runtime (Any, zo, zu)
import GHC.Word (Word(W#))

type ZNat = Word

data ZOverflow = ZOverflow

instance Show ZOverflow where
  show _ = "leanzempic: Nat overflow (value exceeds 2^64-1 in word mode)"

instance Exception ZOverflow

overflow :: a
overflow = throw ZOverflow
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
natPow x y
  | y == 0 = 1
  | x <= 1 = x
  | otherwise = go 1 y
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

-- Explicit build so GHC's foldr/build fusion always sees the producer.
zRange :: ZNat -> [Any]
zRange n = map zo (build (\c nil ->
  let go !i = if i >= n then nil else i `c` go (i + 1) in go 0))
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

-- BEGIN GENERATED (tools/gen_runtime.py)
-- Conversions between Nat and the fixed-width integers.
u8OfNat :: ZNat -> Word8
u8OfNat = fromIntegral
u8ToNat :: Word8 -> ZNat
u8ToNat = fromIntegral
{-# INLINE u8OfNat #-}
{-# INLINE u8ToNat #-}
u16OfNat :: ZNat -> Word16
u16OfNat = fromIntegral
u16ToNat :: Word16 -> ZNat
u16ToNat = fromIntegral
{-# INLINE u16OfNat #-}
{-# INLINE u16ToNat #-}
u32OfNat :: ZNat -> Word32
u32OfNat = fromIntegral
u32ToNat :: Word32 -> ZNat
u32ToNat = fromIntegral
{-# INLINE u32OfNat #-}
{-# INLINE u32ToNat #-}
u64OfNat :: ZNat -> Word64
u64OfNat = fromIntegral
u64ToNat :: Word64 -> ZNat
u64ToNat = fromIntegral
{-# INLINE u64OfNat #-}
{-# INLINE u64ToNat #-}
uszOfNat :: ZNat -> Word
uszOfNat = fromIntegral
uszToNat :: Word -> ZNat
uszToNat = fromIntegral
{-# INLINE uszOfNat #-}
{-# INLINE uszToNat #-}
charOfNat :: ZNat -> Word32
charOfNat n = if n < 55296 || (n > 57343 && n < 1114112) then fromIntegral n else 0
charOfNatAux :: ZNat -> Any -> Word32
charOfNatAux n _ = fromIntegral n
{-# INLINE charOfNat #-}
{-# INLINE charOfNatAux #-}
-- END GENERATED
