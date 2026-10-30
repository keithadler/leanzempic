-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's List is Haskell's [] (elements are Any). The combinators are thin
-- wrappers over base functions that have foldr/build fusion rules.
{-# LANGUAGE BangPatterns #-}
module Zempic.List where

import Data.List (foldl')
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

zAppend :: [Any] -> [Any] -> [Any]
zAppend = (++)
{-# INLINE zAppend #-}

zFoldr :: (Any -> Any -> Any) -> Any -> [Any] -> Any
zFoldr = foldr
{-# INLINE zFoldr #-}

zAny, zAll :: (Any -> Any) -> [Any] -> Bool
zAny p = foldr (\x r -> (zu (p x) :: Bool) || r) False
zAll p = foldr (\x r -> (zu (p x) :: Bool) && r) True
{-# INLINE zAny #-}
{-# INLINE zAll #-}

zZip :: [Any] -> [Any] -> [Any]
zZip = zipWith (\a b -> zo (a, b))
{-# INLINE zZip #-}

zPair :: Any -> Any -> a -> b -> (a, b)
zPair _ _ a b = (a, b)
{-# INLINE zPair #-}
