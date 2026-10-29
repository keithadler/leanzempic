-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's Array as a persistent array in the style of Baker (1978), as in Data.Array.Diff.
--
-- Lean mutates an array in place when nothing else refers to it, which it knows from reference
-- counts. GHC has no such counts, so a pure `set` must leave the old array intact. A version
-- here is either the live buffer or a short undo record pointing at a newer version. Using the
-- newest version, as a loop does, costs O(1) with no copying; reading an old version "reroots"
-- the buffer back to it, which is slower but always correct.
{-# LANGUAGE BangPatterns #-}
module Zempic.Arr
  ( Arr, aEmpty, aReplicate, aLength, aGet, aSet, aPush, aPop, aSwap, aToList, aFromList
  , aSetU, aPushU, aPopU, aSwapU
  ) where

import Control.Monad (forM_)
import Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, newArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

-- | How to get from the newer version this node points at to the version holding the node.
data Op
  = OSet !Int Any  -- ^ same length, element @i@ was this value
  | OPop           -- ^ one element shorter
  | OPush Any      -- ^ one element longer, ending in this value
  | OSwap !Int !Int -- ^ same length, elements @i@ and @j@ were exchanged (its own inverse)

data Node = Direct !(IOArray Int Any) | Diff !Op !Arr

-- | One version of an array: its length never changes, its contents live behind the reference.
data Arr = Arr { aLen :: !Int, aRef :: !(IORef Node) }

filler :: Any
filler = unsafeCoerce ()

newBuf :: Int -> Any -> IO (IOArray Int Any)
newBuf n x = newArray (0, max 0 (n - 1)) x

aEmpty :: Int -> IO Arr
aEmpty cap = do
  buf <- newBuf (max 4 (min cap 1048576)) filler
  Arr 0 <$> newIORef (Direct buf)

aReplicate :: Int -> Any -> IO Arr
aReplicate n v = do
  buf <- newBuf n v
  Arr (max 0 n) <$> newIORef (Direct buf)

aLength :: Arr -> Int
aLength = aLen

-- | Make this version the live one and return its buffer.
reroot :: Arr -> IO (IOArray Int Any)
reroot arr = do
  node <- readIORef (aRef arr)
  case node of
    Direct buf -> return buf
    Diff op next -> do
      buf <- reroot next
      case op of
        OSet i old -> do
          cur <- unsafeRead buf i
          unsafeWrite buf i old
          writeIORef (aRef next) (Diff (OSet i cur) arr)
        OPop -> do
          v <- unsafeRead buf (aLen arr)
          writeIORef (aRef next) (Diff (OPush v) arr)
        OPush v -> do
          unsafeWrite buf (aLen arr - 1) v
          writeIORef (aRef next) (Diff OPop arr)
        OSwap i j -> do
          x <- unsafeRead buf i
          y <- unsafeRead buf j
          unsafeWrite buf i y
          unsafeWrite buf j x
          writeIORef (aRef next) (Diff (OSwap i j) arr)
      writeIORef (aRef arr) (Direct buf)
      return buf

aGet :: Arr -> Int -> Any -> IO Any
aGet arr i d
  | i < 0 || i >= aLen arr = return d
  | otherwise = do
      buf <- reroot arr
      unsafeRead buf i

-- | Out-of-bounds sets leave the array unchanged, as in Lean.
aSet :: Arr -> Int -> Any -> IO Arr
aSet arr i v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      buf <- reroot arr
      old <- unsafeRead buf i
      unsafeWrite buf i v
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr) ref
      writeIORef (aRef arr) (Diff (OSet i old) arr')
      return arr'

aPush :: Arr -> Any -> IO Arr
aPush arr v = do
  buf <- reroot arr
  cap <- getNumElements buf
  let n = aLen arr
  buf' <-
    if n < cap
      then return buf
      else do
        b <- newBuf (max 4 (2 * cap)) filler
        let copy :: Int -> IO ()
            copy !k | k >= n = return ()
                    | otherwise = unsafeRead buf k >>= unsafeWrite b k >> copy (k + 1)
        copy 0
        return b
  unsafeWrite buf' n v
  ref <- newIORef (Direct buf')
  let arr' = Arr (n + 1) ref
  writeIORef (aRef arr) (Diff OPop arr')
  return arr'

aPop :: Arr -> IO Arr
aPop arr
  | aLen arr == 0 = return arr
  | otherwise = do
      buf <- reroot arr
      v <- unsafeRead buf (aLen arr - 1)
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr - 1) ref
      writeIORef (aRef arr) (Diff (OPush v) arr')
      return arr'

aSwap :: Arr -> Int -> Int -> IO Arr
aSwap arr i j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      buf <- reroot arr
      x <- unsafeRead buf i
      y <- unsafeRead buf j
      unsafeWrite buf i y
      unsafeWrite buf j x
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr) ref
      writeIORef (aRef arr) (Diff (OSwap i j) arr')
      return arr'

aToList :: Arr -> IO [Any]
aToList arr = do
  buf <- reroot arr
  mapM (unsafeRead buf) [0 .. aLen arr - 1]

aFromList :: [Any] -> IO Arr
aFromList xs = do
  let n = length xs
  buf <- newBuf (max 4 n) filler
  forM_ (zip [0 ..] xs) $ \(k, x) -> unsafeWrite buf k x
  Arr n <$> newIORef (Direct buf)

-- * In-place variants
--
-- The compiler calls these only where its ownership analysis proved the array has exactly one
-- reference and is not used again. They update the live buffer directly with no undo record. As a
-- safety net, if the array turns out not to be the live version they fall back to the persistent
-- operation, which is always correct.

aSetU :: Arr -> Int -> Any -> IO Arr
aSetU arr i v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct buf -> unsafeWrite buf i v >> return arr
        Diff _ _ -> aSet arr i v

aPushU :: Arr -> Any -> IO Arr
aPushU arr v = do
  node <- readIORef (aRef arr)
  case node of
    Diff _ _ -> aPush arr v
    Direct buf -> do
      cap <- getNumElements buf
      let n = aLen arr
      if n < cap
        then unsafeWrite buf n v
        else do
          b <- newBuf (max 4 (2 * cap)) filler
          let copy :: Int -> IO ()
              copy !k | k >= n = return ()
                      | otherwise = unsafeRead buf k >>= unsafeWrite b k >> copy (k + 1)
          copy 0
          unsafeWrite b n v
          writeIORef (aRef arr) (Direct b)
      return (Arr (n + 1) (aRef arr))

aPopU :: Arr -> IO Arr
aPopU arr
  | aLen arr == 0 = return arr
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct _ -> return (Arr (aLen arr - 1) (aRef arr))
        Diff _ _ -> aPop arr

aSwapU :: Arr -> Int -> Int -> IO Arr
aSwapU arr i j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct buf -> do
          x <- unsafeRead buf i
          y <- unsafeRead buf j
          unsafeWrite buf i y
          unsafeWrite buf j x
          return arr
        Diff _ _ -> aSwap arr i j
