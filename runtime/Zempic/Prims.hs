-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Runtime pieces that do not depend on how Nat is represented: Int as Integer, Float as Double,
-- Thunk (lazy), and the hash mixer.
module Zempic.Prims where

import Data.Bits (shiftR, xor)
import Data.Ratio ((%))
import Data.Word (Word64)
import Zempic.Runtime (Any, erased, zo, zu)

-- Int ------------------------------------------------------------------------------------------
intAdd, intSub, intMul, intEDiv, intEMod, intTDiv, intTMod, intFDiv, intFMod :: Integer -> Integer -> Integer
intAdd = (+)
intSub = (-)
intMul = (*)
-- Euclidean division, as Lean's @/@ and @%@ on Int; x / 0 = 0 and x % 0 = x.
intEDiv x y
  | y == 0 = 0
  | r < 0 = if y > 0 then q - 1 else q + 1
  | otherwise = q
  where (q, r) = quotRem x y
intEMod x y
  | y == 0 = x
  | r < 0 = r + abs y
  | otherwise = r
  where r = rem x y
intTDiv x y = if y == 0 then 0 else quot x y
intTMod x y = if y == 0 then x else rem x y
intFDiv x y = if y == 0 then 0 else div x y
intFMod x y = if y == 0 then x else mod x y

intNeg :: Integer -> Integer
intNeg = negate

intEq, intLt, intLe :: Integer -> Integer -> Bool
intEq = (==)
intLt = (<)
intLe = (<=)

intIsNeg :: Integer -> Bool
intIsNeg = (< 0)

-- Float ----------------------------------------------------------------------------------------
floatAdd, floatSub, floatMul, floatDiv, floatPow, floatAtan2 :: Double -> Double -> Double
floatAdd = (+)
floatSub = (-)
floatMul = (*)
floatDiv = (/)
floatPow = (**)
floatAtan2 = atan2

floatNeg, floatSqrt, floatSin, floatCos, floatTan, floatExp, floatLog, floatAbs, floatFloor,
  floatCeil, floatRound, floatAtan, floatAsin, floatAcos, floatSinh, floatCosh, floatTanh,
  floatLog2, floatLog10, floatExp2 :: Double -> Double
floatNeg = negate
floatSqrt = sqrt
floatSin = sin
floatCos = cos
floatTan = tan
floatExp = exp
floatLog = log
floatLog2 = logBase 2
floatLog10 = logBase 10
floatExp2 = (2 **)
floatAbs = abs
floatFloor x = if isNaN x || isInfinite x then x else fromInteger (floor x)
floatCeil x = if isNaN x || isInfinite x then x else fromInteger (ceiling x)
-- C's round: half away from zero.
floatRound x
  | isNaN x || isInfinite x = x
  | x >= 0 = fromInteger (floor (x + 0.5))
  | otherwise = negate (fromInteger (floor (negate x + 0.5)))
floatAtan = atan
floatAsin = asin
floatAcos = acos
floatSinh = sinh
floatCosh = cosh
floatTanh = tanh

floatEq, floatLt, floatLe :: Double -> Double -> Bool
floatEq = (==)
floatLt = (<)
floatLe = (<=)

floatIsNaN, floatIsInf, floatIsFinite :: Double -> Bool
floatIsNaN = isNaN
floatIsInf = isInfinite
floatIsFinite x = not (isNaN x || isInfinite x)

-- | Lean's saturating conversion to an unsigned type of the given maximum: NaN and negatives are 0.
floatToUnsigned :: Integer -> Double -> Integer
floatToUnsigned mx x
  | isNaN x || x <= 0 = 0
  | x >= fromInteger mx = mx
  | otherwise = truncate x

-- | @m * 10^(-e)@ if the flag is set, else @m * 10^e@, correctly rounded.
floatOfSci :: Integer -> Bool -> Integer -> Double
floatOfSci m neg e
  | neg = fromRational (m % (10 ^ e))
  | otherwise = fromRational ((m * 10 ^ e) % 1)

-- Thunk (lazy) ---------------------------------------------------------------------------------
data ZThunk = ZThunk Any

thunkMk :: Any -> Any -> Any
thunkMk _ f = zo (ZThunk ((zu f :: Any -> Any) erased))

thunkPure :: Any -> Any -> Any
thunkPure _ a = zo (ZThunk a)

thunkGet :: Any -> Any -> Any
thunkGet _ t = case (zu t :: ZThunk) of ZThunk v -> v

-- Hash -----------------------------------------------------------------------------------------
mixHash :: Word64 -> Word64 -> Word64
mixHash h k0 =
  let m = 0xc6a4a7935bd1e995
      k1 = k0 * m
      k2 = k1 `xor` (k1 `shiftR` 47)
      k3 = k2 `xor` m
  in (h `xor` k3) * m
