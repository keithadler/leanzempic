-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Runtime for leanzempic output. Every Lean value is an `Any`; the casts are
-- free (they vanish in Core), so GHC still sees through them.
module Zempic.Runtime (module Zempic.Runtime, Any) where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import GHC.Exts (Any)
import Numeric.Natural (Natural)
import Unsafe.Coerce (unsafeCoerce)

zo :: a -> Any
zo = unsafeCoerce
{-# INLINE zo #-}

zu :: Any -> a
zu = unsafeCoerce
{-# INLINE zu #-}

zap :: Any -> Any -> Any
zap f x = (unsafeCoerce f :: Any -> Any) x
{-# INLINE zap #-}

erased :: Any
erased = zo ()

hsTrue, hsFalse, natZero :: Any
hsTrue = zo True
hsFalse = zo False
natZero = zo (0 :: Natural)

nat2 :: (Natural -> Natural -> b) -> Any -> Any -> Any
nat2 f a b = zo (f (zu a) (zu b))
{-# INLINE nat2 #-}

natAdd, natSub, natMul, natDiv, natMod, natPow, natEq, natLt, natLe :: Any -> Any -> Any
natAdd = nat2 (+)
natSub = nat2 (\x y -> if x >= y then x - y else 0)
natMul = nat2 (*)
natDiv = nat2 (\x y -> if y == 0 then 0 else quot x y)
natMod = nat2 (\x y -> if y == 0 then x else rem x y)
natPow = nat2 (^)
natEq = nat2 (==)
natLt = nat2 (<)
natLe = nat2 (<=)
{-# INLINE natAdd #-}
{-# INLINE natSub #-}
{-# INLINE natMul #-}
{-# INLINE natDiv #-}
{-# INLINE natMod #-}
{-# INLINE natPow #-}
{-# INLINE natEq #-}
{-# INLINE natLt #-}
{-# INLINE natLe #-}

natShr, natShl, natAnd, natOr, natXor, natGcd :: Any -> Any -> Any
natShr = nat2 (\x y -> shiftR x (fromIntegral y))
natShl = nat2 (\x y -> shiftL x (fromIntegral y))
natAnd = nat2 (.&.)
natOr = nat2 (.|.)
natXor = nat2 xor
natGcd = nat2 gcd
{-# INLINE natShr #-}
{-# INLINE natShl #-}
{-# INLINE natAnd #-}
{-# INLINE natOr #-}
{-# INLINE natXor #-}
{-# INLINE natGcd #-}

natSucc :: Any -> Any
natSucc a = zo ((zu a :: Natural) + 1)
{-# INLINE natSucc #-}
