-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Glue for auto mode: run the Word version, fall back to the exact one on overflow.
-- Sound because generated code is pure: rerunning gives the exact answer.
module Zempic.Auto (tryFast, toW) where

import Control.Exception (evaluate, throw, try)
import Numeric.Natural (Natural)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Zempic.Nat.Word (ZOverflow (..))

tryFast :: (a -> b) -> a -> b -> b
tryFast conv fast exact = unsafeDupablePerformIO $ do
  r <- try (evaluate (conv fast))
  return $ case r of
    Left ZOverflow -> exact
    Right v -> v
{-# NOINLINE tryFast #-}

toW :: Natural -> Word
toW n
  | n > fromIntegral (maxBound :: Word) = throw ZOverflow
  | otherwise = fromIntegral n
{-# INLINE toW #-}
