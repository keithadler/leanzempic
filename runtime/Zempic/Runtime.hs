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

