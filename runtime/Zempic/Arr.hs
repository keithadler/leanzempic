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
  , aSetU, aPushU, aPopU, aSwapU, aDeopt, aShare
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

-- | A live buffer carries the number of undo records hanging off it. When that outgrows the array a
-- write starts a fresh copy instead, so a long-lived old version never pins an unbounded chain. The
-- version a copy was taken from is marked with count -1: it still reads correctly, but the in-place
-- variants must not trust it as the sole owner.
--
-- A @Lazy@ version is a handle that has not copied anything yet: it reads through to the version it
-- was made from, and copies the buffer the first time it is written. It is how a shared array is
-- handed to code that will mutate it (`aShare`): Lean does the same copy-on-first-write with its
-- reference counts, and a function that never writes costs nothing.
data Node = Direct !Buf !Int | Diff !Op !Arr | Lazy !Arr

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
  Arr 0 <$> newIORef (Direct buf 0)

aEmpty :: Int -> IO Arr
aEmpty = aEmptyK 0

aReplicateK :: Int -> Int -> Any -> IO Arr
aReplicateK kind n v = do
  buf <- bufNewFilled kind n v
  Arr (max 0 n) <$> newIORef (Direct buf 0)

aReplicate :: Int -> Any -> IO Arr
aReplicate = aReplicateK 0

aLength :: Arr -> Int
aLength = aLen

-- | Make this version the live one; the result is its @Direct@ node (buffer and undo-record count).
-- Rerooting only moves a record from one side of the buffer to the other, so the count is unchanged.
rerootN :: Arr -> IO Node
rerootN arr = do
  node <- readIORef (aRef arr)
  case node of
    Direct _ _ -> return node
    Lazy src -> do
      -- Copy now. A chain of lazy handles is cut to its end first, so there is one copy, not several.
      end <- lazyEnd src
      nn <- rerootN end
      case nn of
        Direct buf _ -> do
          b' <- bufClone buf (aLen end)
          let d = Direct b' 0
          writeIORef (aRef arr) d
          return d
        _ -> error "rerootN"
    Diff op next -> do
      nn <- rerootN next
      case nn of
        Direct buf c -> do
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
          let d = Direct buf c
          writeIORef (aRef arr) d
          return d
        Diff _ _ -> return nn  -- cannot happen: rerootN returns a Direct node

reroot :: Arr -> IO Buf
reroot arr = do
  nd <- rerootN arr
  case nd of
    Direct buf _ -> return buf
    Diff _ _ -> error "reroot"

-- | The version a chain of lazy handles ends at.
lazyEnd :: Arr -> IO Arr
lazyEnd a = do
  node <- readIORef (aRef a)
  case node of
    Lazy s -> lazyEnd s
    _ -> return a

-- | A handle that will copy the array when it is first written, and reads through until then.
aShare :: Arr -> IO Arr
aShare src = do
  end <- lazyEnd src
  Arr (aLen end) <$> newIORef (Lazy end)

-- | How many undo records a buffer may carry before the next write copies it.
chainLimit :: Int -> Int
chainLimit n = max 64 n
{-# INLINE chainLimit #-}

-- | A fresh buffer holding the same elements and capacity (the old one keeps serving older versions).
bufClone :: Buf -> Int -> IO Buf
bufClone b n = do
  cap <- bufCap b
  bufGrow b n cap

aGet :: Arr -> Int -> Any -> IO Any
aGet arr i d
  | i < 0 || i >= aLen arr = return d
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct buf _ -> bufRead buf i
        Lazy src -> aGet src i d
        _ -> do
          buf <- reroot arr
          bufRead buf i

-- | Out-of-bounds sets leave the array unchanged, as in Lean.
aSet :: Arr -> Int -> Any -> IO Arr
aSet arr i v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      nd <- rerootN arr
      case nd of
        Direct buf c
          | c >= chainLimit (aLen arr) || c < 0 -> do
              b' <- bufClone buf (aLen arr)
              bufWrite b' i v
              writeIORef (aRef arr) (Direct buf (-1))
              Arr (aLen arr) <$> newIORef (Direct b' 0)
          | otherwise -> do
              old <- bufRead buf i
              bufWrite buf i v
              ref <- newIORef (Direct buf (c + 1))
              let arr' = Arr (aLen arr) ref
              writeIORef (aRef arr) (Diff (OSet i old) arr')
              return arr'
        Diff _ _ -> return arr

aPush :: Arr -> Any -> IO Arr
aPush arr v = do
  nd <- rerootN arr
  case nd of
    Direct buf c -> do
      cap <- bufCap buf
      let n = aLen arr
      if n >= cap || c >= chainLimit n || c < 0
        then do
          buf' <- bufGrow buf n (if n < cap then cap else max 4 (2 * cap))
          bufWrite buf' n v
          writeIORef (aRef arr) (Direct buf (-1))
          Arr (n + 1) <$> newIORef (Direct buf' 0)
        else do
          bufWrite buf n v
          ref <- newIORef (Direct buf (c + 1))
          let arr' = Arr (n + 1) ref
          writeIORef (aRef arr) (Diff OPop arr')
          return arr'
    Diff _ _ -> return arr

aPop :: Arr -> IO Arr
aPop arr
  | aLen arr == 0 = return arr
  | otherwise = do
      nd <- rerootN arr
      case nd of
        Direct buf c
          | c < 0 -> do
              b' <- bufClone buf (aLen arr)
              Arr (aLen arr - 1) <$> newIORef (Direct b' 0)
          | otherwise -> do
              v <- bufRead buf (aLen arr - 1)
              ref <- newIORef (Direct buf (c + 1))
              let arr' = Arr (aLen arr - 1) ref
              writeIORef (aRef arr) (Diff (OPush v) arr')
              return arr'
        Diff _ _ -> return arr

aSwap :: Arr -> Int -> Int -> IO Arr
aSwap arr i j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      nd <- rerootN arr
      case nd of
        Direct buf c
          | c >= chainLimit (aLen arr) || c < 0 -> do
              b' <- bufClone buf (aLen arr)
              x <- bufRead b' i
              y <- bufRead b' j
              bufWrite b' i y
              bufWrite b' j x
              writeIORef (aRef arr) (Direct buf (-1))
              Arr (aLen arr) <$> newIORef (Direct b' 0)
          | otherwise -> do
              x <- bufRead buf i
              y <- bufRead buf j
              bufWrite buf i y
              bufWrite buf j x
              ref <- newIORef (Direct buf (c + 1))
              let arr' = Arr (aLen arr) ref
              writeIORef (aRef arr) (Diff (OSwap i j) arr')
              return arr'
        Diff _ _ -> return arr

aToList :: Arr -> IO [Any]
aToList arr = do
  node <- readIORef (aRef arr)
  case node of
    Lazy src -> aToList src
    _ -> do
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
  Arr n <$> newIORef (Direct buf 0)

aFromList :: [Any] -> IO Arr
aFromList = aFromListK 0

-- * In-place variants
--
-- The compiler calls these only where its ownership analysis proved the array has exactly one
-- reference and is not used again. They update the live buffer directly with no undo record. As a
-- safety net, if the array turns out not to be the live version they fall back to the persistent
-- operation, which is always correct.

-- | The node of an array about to be updated in place: a lazy handle is copied first.
ownNode :: Arr -> IO Node
ownNode arr = do
  node <- readIORef (aRef arr)
  case node of
    Lazy _ -> rerootN arr
    _ -> return node

aSetU :: Arr -> Int -> Any -> IO Arr
aSetU arr i v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      node <- ownNode arr
      case node of
        Direct buf c | c >= 0 -> bufWrite buf i v >> return arr
        _ -> aSet arr i v

aPushU :: Arr -> Any -> IO Arr
aPushU arr v = do
  node <- ownNode arr
  case node of
    Diff _ _ -> aPush arr v
    Direct _ c | c < 0 -> aPush arr v
    Direct buf c -> do
      cap <- bufCap buf
      let n = aLen arr
      if n < cap
        then bufWrite buf n v
        else do
          b <- bufGrow buf n (max 4 (2 * cap))
          bufWrite b n v
          writeIORef (aRef arr) (Direct b c)
      return (Arr (n + 1) (aRef arr))

aPopU :: Arr -> IO Arr
aPopU arr
  | aLen arr == 0 = return arr
  | otherwise = do
      node <- ownNode arr
      case node of
        Direct _ c | c >= 0 -> return (Arr (aLen arr - 1) (aRef arr))
        _ -> aPop arr

aSwapU :: Arr -> Int -> Int -> IO Arr
aSwapU arr i j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      node <- ownNode arr
      case node of
        Direct buf c | c >= 0 -> do
          x <- bufRead buf i
          y <- bufRead buf j
          bufWrite buf i y
          bufWrite buf j x
          return arr
        _ -> aSwap arr i j

-- | Make this array's buffer boxed. Code that views an array as boxed values of a different type
-- (Lean's in-place `Array.map` does) must not write into an unboxed buffer, so it converts first. The
-- live buffer is replaced; older versions reach it through their undo records and see boxed elements.
aDeopt :: Arr -> IO ()
aDeopt arr = do
  nd <- rerootN arr
  case nd of
   Diff _ _ -> return ()
   Direct buf c -> case buf of
    BBox _ -> return ()
    _ -> do
      cap <- bufCap buf
      b <- newArray (0, max 0 (cap - 1)) filler
      let copy :: Int -> IO ()
          copy !k | k >= aLen arr = return ()
                  | otherwise = bufRead buf k >>= unsafeWrite b k >> copy (k + 1)
      copy 0
      writeIORef (aRef arr) (Direct (BBox b) c)
