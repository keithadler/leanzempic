-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's List is Haskell's [] (elements are Any). The combinators are thin
-- wrappers over base functions that have foldr/build fusion rules.
{-# LANGUAGE BangPatterns #-}
module Zempic.List where

import Data.List (foldl')
import GHC.Exts (build)
import Zempic.Nat
import Zempic.Runtime

zNil :: Any -> [Any]
zNil _ = []
{-# INLINE zNil #-}

zCons :: Any -> Any -> [Any] -> [Any]
zCons _ h t = h : t
{-# INLINE zCons #-}

zMap :: (Any -> Any) -> [Any] -> [Any]
zMap = map
{-# INLINE zMap #-}

zFilter :: (Any -> Any) -> [Any] -> [Any]
zFilter p = filter (\x -> zu (p x) :: Bool)
{-# INLINE zFilter #-}

zFoldl :: (Any -> Any -> Any) -> Any -> [Any] -> Any
zFoldl = foldl'
{-# INLINE zFoldl #-}

-- Explicit build so GHC's foldr/build fusion always sees the producer.
zRange :: ZNat -> [Any]
zRange n = map zo (build (\c nil ->
  let go !i = if i >= n then nil else i `c` go (i + 1) in go 0))
{-# INLINE zRange #-}
