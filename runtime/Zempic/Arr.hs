-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's Array as a persistent array in the style of Baker (1978), as in Data.Array.Diff.
--
-- Lean mutates an array in place when nothing else refers to it, which it knows from reference
-- counts. GHC has no such counts, so a pure `set` must leave the old array intact. A version
-- here is either the live buffer or a short undo record pointing at a newer version. Using the
-- newest version, as a loop does, costs O(1) with no copying; reading an old version "reroots"
-- the buffer back to it, which is slower but always correct.
--
-- The buffer has a representation chosen when the array is made. Anything can be boxed (`Any`),
-- which is what generic code uses. When the compiler knows the element type it asks for an unboxed
-- buffer of that type (UInt8/16/32/64, Bool, Char, USize, and Nat in word mode): no pointer per
-- element, nothing for the garbage collector to scan or copy, and no box allocated per stored
-- value. Every operation dispatches on the buffer, so a function that does not know the element
-- type still works on either; an unboxed array just hands back a freshly boxed element.
{-# LANGUAGE BangPatterns, FlexibleContexts, MagicHash #-}
module Zempic.Arr
  ( Arr, aEmpty, aEmptyK, aReplicate, aReplicateK, aLength, aGet, aSet, aPush, aPop, aSwap
  , aToList, aFromList, aFromListK
  , aSetU, aPushU, aPopU, aSwapU, aDeopt
  ) where

import Data.Array.Base (MArray, getNumElements, unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, IOUArray, newArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.Exts (Any, isTrue#, reallyUnsafePtrEquality#)
import Unsafe.Coerce (unsafeCoerce)

-- | The element storage. Kind codes: 0 boxed, 1 Word8, 2 Word16, 3 Word32, 4 Word64, 5 Word,
-- 6 Bool. (@Word@ and @Word64@ are different types with different boxes, so they stay apart.)
data Buf
  = BBox !(IOArray Int Any)
  | B8 !(IOUArray Int Word8)
  | B16 !(IOUArray Int Word16)
  | B32 !(IOUArray Int Word32)
  | B64 !(IOUArray Int Word64)
  | BW !(IOUArray Int Word)
  | BBool !(IOUArray Int Word8)

-- | How to get from the newer version this node points at to the version holding the node.
data Op
  = OSet !Int Any  -- ^ same length, element @i@ was this value
  | OPop           -- ^ one element shorter
  | OPush Any      -- ^ one element longer, ending in this value
  | OSwap !Int !Int -- ^ same length, elements @i@ and @j@ were exchanged (its own inverse)

data Node = Direct !Buf | Diff !Op !Arr

-- | One version of an array: its length never changes, its contents live behind the reference.
data Arr = Arr { aLen :: !Int, aRef :: !(IORef Node) }

filler :: Any
filler = unsafeCoerce ()

-- * Buffers

bufNew :: Int -> Int -> IO Buf
bufNew kind n = case kind of
  1 -> B8 <$> newArray (0, m) 0
  2 -> B16 <$> newArray (0, m) 0
  3 -> B32 <$> newArray (0, m) 0
  4 -> B64 <$> newArray (0, m) 0
  5 -> BW <$> newArray (0, m) 0
  6 -> BBool <$> newArray (0, m) 0
  _ -> BBox <$> newArray (0, m) filler
  where m = max 0 (n - 1)

-- | A buffer of @n@ slots all holding the element @x@.
bufNewFilled :: Int -> Int -> Any -> IO Buf
bufNewFilled kind n x
  | kind == 0 = BBox <$> newArray (0, max 0 (n - 1)) x
  | otherwise = do
      b <- bufNew kind n
      let go :: Int -> IO ()
          go !k | k >= n = return ()
                | otherwise = bufWrite b k x >> go (k + 1)
      go 0
      return b

bufCap :: Buf -> IO Int
bufCap b = case b of
  BBox a -> getNumElements a
  B8 a -> getNumElements a
  B16 a -> getNumElements a
  B32 a -> getNumElements a
  B64 a -> getNumElements a
  BW a -> getNumElements a
  BBool a -> getNumElements a

bufRead :: Buf -> Int -> IO Any
bufRead b i = case b of
  BBox a -> unsafeRead a i
  B8 a -> unsafeCoerce <$> unsafeRead a i
  B16 a -> unsafeCoerce <$> unsafeRead a i
  B32 a -> unsafeCoerce <$> unsafeRead a i
  B64 a -> unsafeCoerce <$> unsafeRead a i
  BW a -> unsafeCoerce <$> unsafeRead a i
  BBool a -> (\w -> unsafeCoerce (w /= 0)) <$> unsafeRead a i
{-# INLINE bufRead #-}

-- | Is this the unit value? Lean's library stores `box(0)` in a slot to drop a reference before a
-- value is written back (`Array.modify`, `swapAt`). It is not an element of an unboxed buffer, so a raw
-- buffer ignores it: the slot is overwritten with the real value right after, and nothing reads it.
isUnit :: Any -> Bool
isUnit v = case v of
  !v' -> case filler of
    !u -> isTrue# (reallyUnsafePtrEquality# v' u)  -- compare the evaluated closures, not the thunks
{-# INLINE isUnit #-}

-- | Write an element. An unboxed buffer holds only elements of its own type, so it must not be given
-- anything else: the placeholder is skipped here, and code that changes an array's element type in
-- place (`Array.mapMUnsafe`) is compiled to call `aDeopt` first, which makes the buffer boxed.
bufWrite :: Buf -> Int -> Any -> IO ()
bufWrite b i v = case b of
  BBox a -> unsafeWrite a i v
  B8 a -> raw (unsafeWrite a i (unsafeCoerce v))
  B16 a -> raw (unsafeWrite a i (unsafeCoerce v))
  B32 a -> raw (unsafeWrite a i (unsafeCoerce v))
  B64 a -> raw (unsafeWrite a i (unsafeCoerce v))
  BW a -> raw (unsafeWrite a i (unsafeCoerce v))
  BBool a -> raw (unsafeWrite a i (if (unsafeCoerce v :: Bool) then 1 else 0))
  where raw act = if isUnit v then return () else act
{-# INLINE bufWrite #-}

-- | A new buffer of the same kind with room for @cap@ elements and the first @n@ copied over.
bufGrow :: Buf -> Int -> Int -> IO Buf
bufGrow b n cap = case b of
  BBox a -> BBox <$> growWith a n cap filler
  B8 a -> B8 <$> growWith a n cap 0
  B16 a -> B16 <$> growWith a n cap 0
  B32 a -> B32 <$> growWith a n cap 0
  B64 a -> B64 <$> growWith a n cap 0
  BW a -> BW <$> growWith a n cap 0
  BBool a -> BBool <$> growWith a n cap 0

growWith :: (MArray a e IO) => a Int e -> Int -> Int -> e -> IO (a Int e)
growWith a n cap z = do
  b <- newArray (0, max 0 (cap - 1)) z
  let copy :: Int -> IO ()
      copy !k | k >= n = return ()
              | otherwise = unsafeRead a k >>= unsafeWrite b k >> copy (k + 1)
  copy 0
  return b
{-# INLINE growWith #-}

-- * Arrays

aEmptyK :: Int -> Int -> IO Arr
aEmptyK kind cap = do
  buf <- bufNew kind (max 4 (min cap 1048576))
  Arr 0 <$> newIORef (Direct buf)

aEmpty :: Int -> IO Arr
aEmpty = aEmptyK 0

aReplicateK :: Int -> Int -> Any -> IO Arr
aReplicateK kind n v = do
  buf <- bufNewFilled kind n v
  Arr (max 0 n) <$> newIORef (Direct buf)

aReplicate :: Int -> Any -> IO Arr
aReplicate = aReplicateK 0

aLength :: Arr -> Int
aLength = aLen

-- | Make this version the live one and return its buffer.
reroot :: Arr -> IO Buf
reroot arr = do
  node <- readIORef (aRef arr)
  case node of
    Direct buf -> return buf
    Diff op next -> do
      buf <- reroot next
      case op of
        OSet i old -> do
          cur <- bufRead buf i
          bufWrite buf i old
          writeIORef (aRef next) (Diff (OSet i cur) arr)
        OPop -> do
          v <- bufRead buf (aLen arr)
          writeIORef (aRef next) (Diff (OPush v) arr)
        OPush v -> do
          bufWrite buf (aLen arr - 1) v
          writeIORef (aRef next) (Diff OPop arr)
        OSwap i j -> do
          x <- bufRead buf i
          y <- bufRead buf j
          bufWrite buf i y
          bufWrite buf j x
          writeIORef (aRef next) (Diff (OSwap i j) arr)
      writeIORef (aRef arr) (Direct buf)
      return buf

aGet :: Arr -> Int -> Any -> IO Any
aGet arr i d
  | i < 0 || i >= aLen arr = return d
  | otherwise = do
      buf <- reroot arr
      bufRead buf i

-- | Out-of-bounds sets leave the array unchanged, as in Lean.
aSet :: Arr -> Int -> Any -> IO Arr
aSet arr i v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      buf <- reroot arr
      old <- bufRead buf i
      bufWrite buf i v
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr) ref
      writeIORef (aRef arr) (Diff (OSet i old) arr')
      return arr'

aPush :: Arr -> Any -> IO Arr
aPush arr v = do
  buf <- reroot arr
  cap <- bufCap buf
  let n = aLen arr
  buf' <- if n < cap then return buf else bufGrow buf n (max 4 (2 * cap))
  bufWrite buf' n v
  ref <- newIORef (Direct buf')
  let arr' = Arr (n + 1) ref
  writeIORef (aRef arr) (Diff OPop arr')
  return arr'

aPop :: Arr -> IO Arr
aPop arr
  | aLen arr == 0 = return arr
  | otherwise = do
      buf <- reroot arr
      v <- bufRead buf (aLen arr - 1)
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr - 1) ref
      writeIORef (aRef arr) (Diff (OPush v) arr')
      return arr'

aSwap :: Arr -> Int -> Int -> IO Arr
aSwap arr i j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      buf <- reroot arr
      x <- bufRead buf i
      y <- bufRead buf j
      bufWrite buf i y
      bufWrite buf j x
      ref <- newIORef (Direct buf)
      let arr' = Arr (aLen arr) ref
      writeIORef (aRef arr) (Diff (OSwap i j) arr')
      return arr'

aToList :: Arr -> IO [Any]
aToList arr = do
  buf <- reroot arr
  mapM (bufRead buf) [0 .. aLen arr - 1]

aFromListK :: Int -> [Any] -> IO Arr
aFromListK kind xs = do
  let n = length xs
  buf <- bufNew kind (max 4 n)
  let fill :: Int -> [Any] -> IO ()
      fill !_ [] = return ()
      fill !k (y : ys) = bufWrite buf k y >> fill (k + 1) ys
  fill 0 xs
  Arr n <$> newIORef (Direct buf)

aFromList :: [Any] -> IO Arr
aFromList = aFromListK 0

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
        Direct buf -> bufWrite buf i v >> return arr
        Diff _ _ -> aSet arr i v

aPushU :: Arr -> Any -> IO Arr
aPushU arr v = do
  node <- readIORef (aRef arr)
  case node of
    Diff _ _ -> aPush arr v
    Direct buf -> do
      cap <- bufCap buf
      let n = aLen arr
      if n < cap
        then bufWrite buf n v
        else do
          b <- bufGrow buf n (max 4 (2 * cap))
          bufWrite b n v
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
          x <- bufRead buf i
          y <- bufRead buf j
          bufWrite buf i y
          bufWrite buf j x
          return arr
        Diff _ _ -> aSwap arr i j

-- | Make this array's buffer boxed. Code that views an array as boxed values of a different type
-- (Lean's in-place `Array.map` does) must not write into an unboxed buffer, so it converts first. The
-- live buffer is replaced; older versions reach it through their undo records and see boxed elements.
aDeopt :: Arr -> IO ()
aDeopt arr = do
  buf <- reroot arr
  case buf of
    BBox _ -> return ()
    _ -> do
      cap <- bufCap buf
      b <- newArray (0, max 0 (cap - 1)) filler
      let copy :: Int -> IO ()
          copy !k | k >= aLen arr = return ()
                  | otherwise = bufRead buf k >>= unsafeWrite b k >> copy (k + 1)
      copy 0
      writeIORef (aRef arr) (Direct (BBox b))
