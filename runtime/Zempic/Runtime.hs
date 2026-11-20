-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Runtime for leanzempic output. Every Lean value is an `Any`; the casts are
-- free (they vanish in Core), so GHC still sees through them.
module Zempic.Runtime (module Zempic.Runtime, Any) where

import GHC.Exts (Any)
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

-- | `Array.propagateMark xs ys` (Lean 4.36): copies Lean's linearity marker from `xs` to `ys` and
-- returns `ys`. Logically the identity on `ys`; there is no marker here. The arguments are the two
-- erased element types, then `xs`, then `ys`.
propagateMark :: Any -> Any -> Any -> Any -> Any
propagateMark _ _ _ ys = ys
{-# INLINE propagateMark #-}

-- | `String.propagateMark` and `ByteArray.propagateMark`: the same, without type arguments.
propagateMark2 :: Any -> Any -> Any
propagateMark2 _ t = t
{-# INLINE propagateMark2 #-}

