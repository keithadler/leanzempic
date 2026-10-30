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
{-# LANGUAGE BangPatterns, FlexibleContexts, MagicHash, UnboxedTuples #-}
module Zempic.Arr
  ( Arr, aEmpty, aEmptyK, aReplicate, aReplicateK, aLength, aGet, aSet, aPush, aPop, aSwap
  , aToList, aFromList, aFromListK
  , aSetU, aPushU, aPopU, aSwapU, aDeopt, aShare
  , aRangeW, aDeoptW, aGetW, aGetWU, aGetWI, aGetWIS, aPushFromU, aPushUW, aSetUW, aSetUWB, aSetUWBF
  , aGetP8, aGetP16, aGetP32, aGetP64, aGetPS8, aGetPS16, aGetPS32, aGetPS64
  , aSwapU8, aSwapU16, aSwapU32, aSwapU64, aSwapUW, aSwapF8, aSwapF16, aSwapF32, aSwapF64, aSwapFW
  , aSetF8, aSetF16, aSetF32, aSetF64
  , aPushU8, aPushU16, aPushU32, aPushU64, aSetU8, aSetU16, aSetU32, aSetU64
  , HB (..), aHoist8, aHoist16, aHoist32, aHoist64, aHoistW, aHoistBool, hGetD8, hGetD16, hGetD32, hGetD64, hGetDW, hGetBool, hSwap, hSet
  ) where

import Data.Array.Base (MArray, STUArray (..), getNumElements, unsafeRead, unsafeWrite)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Data.Array.IO (IOArray, IOUArray, newArray)
import Data.Array.IO.Internals (IOArray (..), IOUArray (..))
import GHC.Arr (STArray (..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.Exts (readWordArray#, readWord8Array#, readWord16Array#, readWord32Array#, readWord64Array#, Any, Int (I#), Int#, RealWorld, State#, Word (W#), Word#, copyMutableArray#, copyMutableByteArray#, isTrue#, newArray#, newByteArray#, reallyUnsafePtrEquality#, runRW#, setByteArray#, (+#), (-#), (*#), (<#))
import GHC.IO (IO (..))
import GHC.Word (Word16 (W16#), Word32 (W32#), Word64 (W64#), Word8 (W8#))
import Unsafe.Coerce (unsafeCoerce)

-- | The element storage. Kind codes: 0 boxed, 1 Word8, 2 Word16, 3 Word32, 4 Word64, 5 Word,
-- 6 Bool. (@Word@ and @Word64@ are different types with different boxes, so they stay apart.)
data Buf
  = BBox {-# UNPACK #-} !(IOArray Int Any)
  | B8 {-# UNPACK #-} !(IOUArray Int Word8)
  | B16 {-# UNPACK #-} !(IOUArray Int Word16)
  | B32 {-# UNPACK #-} !(IOUArray Int Word32)
  | B64 {-# UNPACK #-} !(IOUArray Int Word64)
  | BW {-# UNPACK #-} !(IOUArray Int Word)
  | BBool {-# UNPACK #-} !(IOUArray Int Word8)

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

-- | Exchange two elements in place, without boxing them.
bufSwap :: Buf -> Int -> Int -> IO ()
bufSwap b i j = case b of
  BBox a -> sw a
  B8 a -> sw a
  B16 a -> sw a
  B32 a -> sw a
  B64 a -> sw a
  BW a -> sw a
  BBool a -> sw a
  where
    sw :: (MArray a e IO) => a Int e -> IO ()
    sw a = do
      x <- unsafeRead a i
      y <- unsafeRead a j
      unsafeWrite a i y
      unsafeWrite a j x
    {-# INLINE sw #-}
{-# INLINE bufSwap #-}

-- | A new buffer of the same kind with room for @cap@ elements and the first @n@ copied over. The
-- copy is one block move, and only the tail beyond the copied elements is cleared.
bufGrow :: Buf -> Int -> Int -> IO Buf
bufGrow b n cap = case b of
  BBox (IOArray a) -> BBox . IOArray <$> growBoxed a n cap
  B8 (IOUArray a) -> B8 . IOUArray <$> growRaw 1 a n cap
  B16 (IOUArray a) -> B16 . IOUArray <$> growRaw 2 a n cap
  B32 (IOUArray a) -> B32 . IOUArray <$> growRaw 4 a n cap
  B64 (IOUArray a) -> B64 . IOUArray <$> growRaw 8 a n cap
  BW (IOUArray a) -> BW . IOUArray <$> growRaw 8 a n cap
  BBool (IOUArray a) -> BBool . IOUArray <$> growRaw 1 a n cap

-- | Grow an unboxed buffer whose elements are @sz@ bytes wide.
growRaw :: Int -> STUArray RealWorld Int e -> Int -> Int -> IO (STUArray RealWorld Int e)
growRaw (I# sz) (STUArray _ _ _ src) (I# n) (I# cap0) = IO $ \s0 ->
  let cap = if isTrue# (cap0 <# 1#) then 1# else cap0
      keep = if isTrue# (n <# cap) then n else cap
  in case newByteArray# (cap *# sz) s0 of
    (# s1, dst #) -> case copyMutableByteArray# src 0# dst 0# (keep *# sz) s1 of
      s2 -> case setByteArray# dst (keep *# sz) ((cap -# keep) *# sz) 0# s2 of
        s3 -> (# s3, STUArray 0 (I# (cap -# 1#)) (I# cap) dst #)
{-# INLINE growRaw #-}

-- | Grow a boxed buffer: the new slots hold the filler, as in a fresh buffer.
growBoxed :: STArray RealWorld Int Any -> Int -> Int -> IO (STArray RealWorld Int Any)
growBoxed (STArray _ _ _ src) (I# n) (I# cap0) = IO $ \s0 ->
  let cap = if isTrue# (cap0 <# 1#) then 1# else cap0
      keep = if isTrue# (n <# cap) then n else cap
  in case newArray# cap filler s0 of
    (# s1, dst #) -> case copyMutableArray# src 0# dst 0# keep s1 of
      s2 -> (# s2, STArray 0 (I# (cap -# 1#)) (I# cap) dst #)

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
              bufSwap buf i j
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
aGet !arr !i d
  | i < 0 || i >= aLen arr = return d
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct buf _ -> bufRead buf i
        Lazy src -> aGet src i d
        _ -> do
          buf <- reroot arr
          bufRead buf i

-- Index arguments are strict so the caller's @arrIdx@ is not allocated as a thunk per call.

-- | Out-of-bounds sets leave the array unchanged, as in Lean.
aSet :: Arr -> Int -> Any -> IO Arr
aSet !arr !i v
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
aSwap !arr !i !j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      nd <- rerootN arr
      case nd of
        Direct buf c
          | c >= chainLimit (aLen arr) || c < 0 -> do
              b' <- bufClone buf (aLen arr)
              bufSwap b' i j
              writeIORef (aRef arr) (Direct buf (-1))
              Arr (aLen arr) <$> newIORef (Direct b' 0)
          | otherwise -> do
              bufSwap buf i j
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
aSetU !arr !i v
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
aSwapU !arr !i !j
  | i < 0 || j < 0 || i >= aLen arr || j >= aLen arr = return arr
  | otherwise = do
      node <- ownNode arr
      case node of
        Direct buf c | c >= 0 -> bufSwap buf i j >> return arr
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

-- * Word-typed operations
--
-- When the compiler knows an element is a `Word` (a `Nat` in word mode, or a `USize`) it calls these
-- instead of the `Any` versions: a `Word` buffer is read and written with no box. The compiler picks
-- them only from the static type of the value, never for a placeholder of unknown type.

-- | The array @[0, 1 .. n-1]@ in a `Word` buffer, filled in one pass.
aRangeW :: Int -> IO Arr
aRangeW n = do
  buf <- bufNew 5 (max 4 n)
  case buf of
    BW a -> do
      let go :: Int -> IO ()
          go !k | k >= n = return ()
                | otherwise = unsafeWrite a k (fromIntegral k) >> go (k + 1)
      go 0
    _ -> return ()
  Arr (max 0 n) <$> newIORef (Direct buf 0)

-- | Read an element as a `Word`.
bufReadW :: Buf -> Int -> IO Word
bufReadW b i = case b of
  BW a -> unsafeRead a i
  _ -> do
    v <- bufRead b i
    return $! (unsafeCoerce v :: Word)
{-# INLINE bufReadW #-}

-- | Write a `Word`. A buffer of another element type is not given one (the caller deoptimizes it).
bufWriteW :: Buf -> Int -> Word -> IO ()
bufWriteW b i@(I# i#) w@(W# w#) = case b of
  BW a -> unsafeWrite a i w
  _ -> bufWriteBoxed b i# w#
{-# INLINE bufWriteW #-}

-- | The write that does need the value boxed. It takes it unboxed, so that a caller never uses its
-- argument boxed, and GHC passes it in a register everywhere else.
bufWriteBoxed :: Buf -> Int# -> Word# -> IO ()
bufWriteBoxed b i# w# = bufWrite b (I# i#) (unsafeCoerce (W# w#))
{-# NOINLINE bufWriteBoxed #-}

-- | Read element @i@ as a @Word@, or the default (not forced unless used) when out of range. It works on
-- unboxed words from end to end, with the common case (the live version, a word buffer) read in line:
-- if the fast and slow paths both returned a boxed 'Word', GHC would merge them at a join point that
-- takes the box and allocate one per read.
aGetWU :: Arr -> Int -> Word -> State# RealWorld -> (# State# RealWorld, Word# #)
aGetWU arr i d s0
  | i < 0 || i >= aLen arr = case d of W# d# -> (# s0, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (BW a) _ -> case unsafeRead a i of IO r -> case r s1 of (# s2, W# w #) -> (# s2, w #)
          _ -> getWP arr i d s1
{-# INLINE aGetWU #-}

aGetW :: Arr -> Int -> Word -> IO Word
aGetW arr i d = IO (\s -> case aGetWU arr i d s of (# s', r #) -> (# s', W# r #))
{-# INLINE aGetW #-}

-- | The read for every case the inline one in 'aGetWU' does not handle, with an unboxed result.
getWP :: Arr -> Int -> Word -> State# RealWorld -> (# State# RealWorld, Word# #)
getWP arr i d s
  | i < 0 || i >= aLen arr = case d of W# d# -> (# s, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s of
        (# s1, node #) -> case node of
          Direct buf _ -> readBuf buf s1
          Lazy src -> getWP src i d s1
          _ -> case reroot arr of
            IO m2 -> case m2 s1 of (# s2, buf #) -> readBuf buf s2
  where
    readBuf buf st = case bufReadW buf i of IO r -> case r st of (# st', W# w #) -> (# st', w #)
{-# NOINLINE getWP #-}

-- | `aGetW` run purely, with an unboxed result: once inlined at a use site, GHC reads the `Word`
-- straight into a register and no box is built. The read itself stays a call to a function GHC does
-- not inline, so it is not moved across the writes around it (every call site is a strict @let@).
aGetWI :: Arr -> Int -> Word -> Word
aGetWI arr i d = case runRW# (aGetWU arr i d) of (# _, r #) -> W# r
{-# INLINE aGetWI #-}

-- | 'aGetWI' for a default that is a real value, taken unboxed: a default built at the call site (the
-- literal in @a[i]!@) is then never boxed, which a lazy default would do on every read.
aGetWIS :: Arr -> Int -> Word -> Word
aGetWIS arr i (W# d#) = case runRW# (aGetWU arr i (W# d#)) of (# _, r #) -> W# r
{-# INLINE aGetWIS #-}

-- | `aPushU` for a `Word` element: a live word buffer with room is written in line.
aPushUW :: Arr -> Word -> IO Arr
aPushUW arr !v = do
  node <- readIORef (aRef arr)
  case node of
    Direct (BW a) c | c >= 0 -> do
      cap <- getNumElements a
      let n = aLen arr
      if n < cap then unsafeWrite a n v >> return (Arr (n + 1) (aRef arr)) else aPushUWFull arr v
    _ -> aPushUWFull arr v
{-# INLINE aPushUW #-}

-- | The rest of 'aPushUW'. The rare paths that need the value boxed are separate functions,
-- so this one takes it unboxed.
aPushUWFull :: Arr -> Word -> IO Arr
aPushUWFull arr !v = do
  node <- ownNode arr
  case node of
    Diff _ _ -> slowPushW arr v
    Direct _ c | c < 0 -> slowPushW arr v
    Direct buf c -> do
      cap <- bufCap buf
      let n = aLen arr
      if n < cap
        then bufWriteW buf n v
        else do
          b <- bufGrow buf n (max 4 (2 * cap))
          bufWriteW b n v
          writeIORef (aRef arr) (Direct b c)
      return (Arr (n + 1) (aRef arr))
{-# NOINLINE aPushUWFull #-}

slowPushW :: Arr -> Word -> IO Arr
slowPushW arr (W# v) = aPush arr (unsafeCoerce (W# v))
{-# NOINLINE slowPushW #-}

-- | `aSetU` for a `Word` element: a live word buffer is written in line.
aSetUW :: Arr -> Int -> Word -> IO Arr
aSetUW arr i !v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (BW a) c | c >= 0 -> unsafeWrite a i v >> return arr
        _ -> aSetUWFull arr i v
{-# INLINE aSetUW #-}

-- | The rest of 'aSetUW'.
aSetUWFull :: Arr -> Int -> Word -> IO Arr
aSetUWFull arr i !v
  | i < 0 || i >= aLen arr = return arr
  | otherwise = do
      node <- ownNode arr
      case node of
        Direct buf c | c >= 0 -> bufWriteW buf i v >> return arr
        _ -> slowSetW arr i v
{-# NOINLINE aSetUWFull #-}

slowSetW :: Arr -> Int -> Word -> IO Arr
slowSetW arr (I# i) (W# v) = aSet arr (I# i) (unsafeCoerce (W# v))
{-# NOINLINE slowSetW #-}

-- | `aSetU` for a `Word` element written through a view as another element type (Lean's in-place
-- `Array.map`): a `Word` or boxed buffer takes the value as it is, any other is made boxed first.
aSetUWB :: Arr -> Int -> Word -> IO Arr
aSetUWB arr !i !v = aDeoptW arr >> aSetUWFull arr i v
{-# NOINLINE aSetUWB #-}

-- | The in-line part of 'aSetUWB' for a caller that wants the array itself back when nothing else is
-- needed (a pure expression that returns its own argument does not rebuild it from its fields): 1# if
-- the write was done in place (or the index is out of range, which changes nothing), 0# if the array is
-- not a live word buffer and the caller must take the slow path.
aSetUWBF :: Arr -> Int -> Word -> State# RealWorld -> (# State# RealWorld, Int# #)
aSetUWBF arr i v s0
  | outOfRange i arr = (# s0, 1# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (BW a) c | c >= 0 -> case unsafeWrite a i v of IO w -> case w s1 of (# s2, _ #) -> (# s2, 1# #)
          -- a boxed buffer takes the value as it is (the array holds pairs, say, and is mapped to numbers)
          Direct (BBox a) c | c >= 0 -> case unsafeWrite a i (unsafeCoerce v) of IO w -> case w s1 of (# s2, _ #) -> (# s2, 1# #)
          _ -> (# s1, 0# #)
{-# INLINE aSetUWBF #-}


-- | `aDeopt`, except that a `Word` buffer is left as it is (it holds exactly what a `Word` write stores).
aDeoptW :: Arr -> IO ()
aDeoptW arr = do
  node <- readIORef (aRef arr)
  case node of
    Direct (BW _) _ -> return ()
    Direct (BBox _) _ -> return ()
    _ -> aDeopt arr
{-# INLINE aDeoptW #-}

-- | Is the index outside the array? One unsigned comparison covers a negative index as well (the length is
-- never negative), so a caller may pass any 64-bit pattern without clamping it first.
outOfRange :: Int -> Arr -> Bool
outOfRange i arr = (fromIntegral i :: Word) >= fromIntegral (aLen arr)
{-# INLINE outOfRange #-}

-- * Narrow-typed operations
--
-- The same as the `Word` operations above for `UInt8`, `UInt16`, `UInt32` and `UInt64` elements (and `Char`,
-- which is a `UInt32`). Each reads or writes a live buffer of its own kind in line with no box; every other
-- case goes to a NOINLINE function that uses the generic (boxed) operations, which handle all buffers.
-- The compiler picks them only from the static type of the element, never in a view as another type.

-- | Read element @i@ as a `Word8`, widened to a `Word#`; the default (not forced unless used) is returned
-- when out of range. Works on unboxed words from end to end so that no box is built (see 'aGetWU').
aGetS8 :: Arr -> Int -> Word8 -> State# RealWorld -> (# State# RealWorld, Word# #)
aGetS8 arr i d s0
  | outOfRange i arr = case (fromIntegral d :: Word) of W# d# -> (# s0, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (B8 a) _ -> case unsafeRead a i of
            IO r -> case r s1 of (# s2, w #) -> case (fromIntegral w :: Word) of W# w# -> (# s2, w# #)
          _ -> getPN 8 arr i (unsafeCoerce d) s1
{-# INLINE aGetS8 #-}

-- | 'aGetS8' run purely; the default is not forced (use for a shared error value).
aGetP8 :: Arr -> Int -> Word8 -> Word8
aGetP8 arr i d = case runRW# (aGetS8 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetP8 #-}

-- | 'aGetP8' for a default that is a real value, taken unboxed.
aGetPS8 :: Arr -> Int -> Word8 -> Word8
aGetPS8 arr i !d = case runRW# (aGetS8 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetPS8 #-}

-- | `aPushU` for a `Word8` element: a live buffer of its kind with room is written in line.
aPushU8 :: Arr -> Word8 -> IO Arr
aPushU8 arr !v = do
  node <- readIORef (aRef arr)
  case node of
    Direct (B8 a) c | c >= 0 -> do
      cap <- getNumElements a
      let k = aLen arr
      if k < cap then unsafeWrite a k v >> return (Arr (k + 1) (aRef arr)) else slowPush8 arr v
    _ -> slowPush8 arr v
{-# INLINE aPushU8 #-}

slowPush8 :: Arr -> Word8 -> IO Arr
slowPush8 arr v = aPushU arr (unsafeCoerce v)
{-# NOINLINE slowPush8 #-}

-- | `aSetU` for a `Word8` element: a live buffer of its kind is written in line. 'aSetF8' says whether it was
-- (an index out of range is a no-op and counts as done); otherwise the caller uses the generic set.
aSetF8 :: Arr -> Int -> Word8 -> IO Bool
aSetF8 arr i !v
  | outOfRange i arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B8 a) c | c >= 0 -> unsafeWrite a i v >> return True
        _ -> return False
{-# INLINE aSetF8 #-}

aSetU8 :: Arr -> Int -> Word8 -> IO Arr
aSetU8 arr i !v = do
  ok <- aSetF8 arr i v
  if ok then return arr else slowSet8 arr i v
{-# INLINE aSetU8 #-}

slowSet8 :: Arr -> Int -> Word8 -> IO Arr
slowSet8 arr i v = aSetU arr i (unsafeCoerce v)
{-# NOINLINE slowSet8 #-}

-- | Read element @i@ as a `Word16`, widened to a `Word#`; the default (not forced unless used) is returned
-- when out of range. Works on unboxed words from end to end so that no box is built (see 'aGetWU').
aGetS16 :: Arr -> Int -> Word16 -> State# RealWorld -> (# State# RealWorld, Word# #)
aGetS16 arr i d s0
  | outOfRange i arr = case (fromIntegral d :: Word) of W# d# -> (# s0, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (B16 a) _ -> case unsafeRead a i of
            IO r -> case r s1 of (# s2, w #) -> case (fromIntegral w :: Word) of W# w# -> (# s2, w# #)
          _ -> getPN 16 arr i (unsafeCoerce d) s1
{-# INLINE aGetS16 #-}

-- | 'aGetS16' run purely; the default is not forced (use for a shared error value).
aGetP16 :: Arr -> Int -> Word16 -> Word16
aGetP16 arr i d = case runRW# (aGetS16 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetP16 #-}

-- | 'aGetP16' for a default that is a real value, taken unboxed.
aGetPS16 :: Arr -> Int -> Word16 -> Word16
aGetPS16 arr i !d = case runRW# (aGetS16 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetPS16 #-}

-- | `aPushU` for a `Word16` element: a live buffer of its kind with room is written in line.
aPushU16 :: Arr -> Word16 -> IO Arr
aPushU16 arr !v = do
  node <- readIORef (aRef arr)
  case node of
    Direct (B16 a) c | c >= 0 -> do
      cap <- getNumElements a
      let k = aLen arr
      if k < cap then unsafeWrite a k v >> return (Arr (k + 1) (aRef arr)) else slowPush16 arr v
    _ -> slowPush16 arr v
{-# INLINE aPushU16 #-}

slowPush16 :: Arr -> Word16 -> IO Arr
slowPush16 arr v = aPushU arr (unsafeCoerce v)
{-# NOINLINE slowPush16 #-}

-- | `aSetU` for a `Word16` element: a live buffer of its kind is written in line. 'aSetF16' says whether it was
-- (an index out of range is a no-op and counts as done); otherwise the caller uses the generic set.
aSetF16 :: Arr -> Int -> Word16 -> IO Bool
aSetF16 arr i !v
  | outOfRange i arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B16 a) c | c >= 0 -> unsafeWrite a i v >> return True
        _ -> return False
{-# INLINE aSetF16 #-}

aSetU16 :: Arr -> Int -> Word16 -> IO Arr
aSetU16 arr i !v = do
  ok <- aSetF16 arr i v
  if ok then return arr else slowSet16 arr i v
{-# INLINE aSetU16 #-}

slowSet16 :: Arr -> Int -> Word16 -> IO Arr
slowSet16 arr i v = aSetU arr i (unsafeCoerce v)
{-# NOINLINE slowSet16 #-}

-- | Read element @i@ as a `Word32`, widened to a `Word#`; the default (not forced unless used) is returned
-- when out of range. Works on unboxed words from end to end so that no box is built (see 'aGetWU').
aGetS32 :: Arr -> Int -> Word32 -> State# RealWorld -> (# State# RealWorld, Word# #)
aGetS32 arr i d s0
  | outOfRange i arr = case (fromIntegral d :: Word) of W# d# -> (# s0, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (B32 a) _ -> case unsafeRead a i of
            IO r -> case r s1 of (# s2, w #) -> case (fromIntegral w :: Word) of W# w# -> (# s2, w# #)
          _ -> getPN 32 arr i (unsafeCoerce d) s1
{-# INLINE aGetS32 #-}

-- | 'aGetS32' run purely; the default is not forced (use for a shared error value).
aGetP32 :: Arr -> Int -> Word32 -> Word32
aGetP32 arr i d = case runRW# (aGetS32 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetP32 #-}

-- | 'aGetP32' for a default that is a real value, taken unboxed.
aGetPS32 :: Arr -> Int -> Word32 -> Word32
aGetPS32 arr i !d = case runRW# (aGetS32 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetPS32 #-}

-- | `aPushU` for a `Word32` element: a live buffer of its kind with room is written in line.
aPushU32 :: Arr -> Word32 -> IO Arr
aPushU32 arr !v = do
  node <- readIORef (aRef arr)
  case node of
    Direct (B32 a) c | c >= 0 -> do
      cap <- getNumElements a
      let k = aLen arr
      if k < cap then unsafeWrite a k v >> return (Arr (k + 1) (aRef arr)) else slowPush32 arr v
    _ -> slowPush32 arr v
{-# INLINE aPushU32 #-}

slowPush32 :: Arr -> Word32 -> IO Arr
slowPush32 arr v = aPushU arr (unsafeCoerce v)
{-# NOINLINE slowPush32 #-}

-- | `aSetU` for a `Word32` element: a live buffer of its kind is written in line. 'aSetF32' says whether it was
-- (an index out of range is a no-op and counts as done); otherwise the caller uses the generic set.
aSetF32 :: Arr -> Int -> Word32 -> IO Bool
aSetF32 arr i !v
  | outOfRange i arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B32 a) c | c >= 0 -> unsafeWrite a i v >> return True
        _ -> return False
{-# INLINE aSetF32 #-}

aSetU32 :: Arr -> Int -> Word32 -> IO Arr
aSetU32 arr i !v = do
  ok <- aSetF32 arr i v
  if ok then return arr else slowSet32 arr i v
{-# INLINE aSetU32 #-}

slowSet32 :: Arr -> Int -> Word32 -> IO Arr
slowSet32 arr i v = aSetU arr i (unsafeCoerce v)
{-# NOINLINE slowSet32 #-}

-- | Read element @i@ as a `Word64`, widened to a `Word#`; the default (not forced unless used) is returned
-- when out of range. Works on unboxed words from end to end so that no box is built (see 'aGetWU').
aGetS64 :: Arr -> Int -> Word64 -> State# RealWorld -> (# State# RealWorld, Word# #)
aGetS64 arr i d s0
  | outOfRange i arr = case (fromIntegral d :: Word) of W# d# -> (# s0, d# #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s0 of
        (# s1, node #) -> case node of
          Direct (B64 a) _ -> case unsafeRead a i of
            IO r -> case r s1 of (# s2, w #) -> case (fromIntegral w :: Word) of W# w# -> (# s2, w# #)
          _ -> getPN 64 arr i (unsafeCoerce d) s1
{-# INLINE aGetS64 #-}

-- | 'aGetS64' run purely; the default is not forced (use for a shared error value).
aGetP64 :: Arr -> Int -> Word64 -> Word64
aGetP64 arr i d = case runRW# (aGetS64 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetP64 #-}

-- | 'aGetP64' for a default that is a real value, taken unboxed.
aGetPS64 :: Arr -> Int -> Word64 -> Word64
aGetPS64 arr i !d = case runRW# (aGetS64 arr i d) of (# _, r #) -> fromIntegral (W# r)
{-# INLINE aGetPS64 #-}

-- | `aPushU` for a `Word64` element: a live buffer of its kind with room is written in line.
aPushU64 :: Arr -> Word64 -> IO Arr
aPushU64 arr !v = do
  node <- readIORef (aRef arr)
  case node of
    Direct (B64 a) c | c >= 0 -> do
      cap <- getNumElements a
      let k = aLen arr
      if k < cap then unsafeWrite a k v >> return (Arr (k + 1) (aRef arr)) else slowPush64 arr v
    _ -> slowPush64 arr v
{-# INLINE aPushU64 #-}

slowPush64 :: Arr -> Word64 -> IO Arr
slowPush64 arr v = aPushU arr (unsafeCoerce v)
{-# NOINLINE slowPush64 #-}

-- | `aSetU` for a `Word64` element: a live buffer of its kind is written in line. 'aSetF64' says whether it was
-- (an index out of range is a no-op and counts as done); otherwise the caller uses the generic set.
aSetF64 :: Arr -> Int -> Word64 -> IO Bool
aSetF64 arr i !v
  | outOfRange i arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B64 a) c | c >= 0 -> unsafeWrite a i v >> return True
        _ -> return False
{-# INLINE aSetF64 #-}

aSetU64 :: Arr -> Int -> Word64 -> IO Arr
aSetU64 arr i !v = do
  ok <- aSetF64 arr i v
  if ok then return arr else slowSet64 arr i v
{-# INLINE aSetU64 #-}

slowSet64 :: Arr -> Int -> Word64 -> IO Arr
slowSet64 arr i v = aSetU arr i (unsafeCoerce v)
{-# NOINLINE slowSet64 #-}

-- | `aSwapU` on a buffer of this kind: the exchange is done in line. 'aSwapF' says whether it was; when it
-- was not, the caller uses the generic swap. It returns a flag, not the array, so that a caller hands back the
-- array it already has and no new 'Arr' record is built.
aSwapF8 :: Arr -> Int -> Int -> IO Bool
aSwapF8 !arr !i !j
  | outOfRange i arr || outOfRange j arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B8 a) c | c >= 0 -> do
          x <- unsafeRead a i
          y <- unsafeRead a j
          unsafeWrite a i y
          unsafeWrite a j x
          return True
        _ -> return False
{-# INLINE aSwapF8 #-}

aSwapU8 :: Arr -> Int -> Int -> IO Arr
aSwapU8 !arr !i !j = do
  ok <- aSwapF8 arr i j
  if ok then return arr else aSwapU arr i j
{-# INLINE aSwapU8 #-}

aSwapF16 :: Arr -> Int -> Int -> IO Bool
aSwapF16 !arr !i !j
  | outOfRange i arr || outOfRange j arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B16 a) c | c >= 0 -> do
          x <- unsafeRead a i
          y <- unsafeRead a j
          unsafeWrite a i y
          unsafeWrite a j x
          return True
        _ -> return False
{-# INLINE aSwapF16 #-}

aSwapU16 :: Arr -> Int -> Int -> IO Arr
aSwapU16 !arr !i !j = do
  ok <- aSwapF16 arr i j
  if ok then return arr else aSwapU arr i j
{-# INLINE aSwapU16 #-}

aSwapF32 :: Arr -> Int -> Int -> IO Bool
aSwapF32 !arr !i !j
  | outOfRange i arr || outOfRange j arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B32 a) c | c >= 0 -> do
          x <- unsafeRead a i
          y <- unsafeRead a j
          unsafeWrite a i y
          unsafeWrite a j x
          return True
        _ -> return False
{-# INLINE aSwapF32 #-}

aSwapU32 :: Arr -> Int -> Int -> IO Arr
aSwapU32 !arr !i !j = do
  ok <- aSwapF32 arr i j
  if ok then return arr else aSwapU arr i j
{-# INLINE aSwapU32 #-}

aSwapF64 :: Arr -> Int -> Int -> IO Bool
aSwapF64 !arr !i !j
  | outOfRange i arr || outOfRange j arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (B64 a) c | c >= 0 -> do
          x <- unsafeRead a i
          y <- unsafeRead a j
          unsafeWrite a i y
          unsafeWrite a j x
          return True
        _ -> return False
{-# INLINE aSwapF64 #-}

aSwapU64 :: Arr -> Int -> Int -> IO Arr
aSwapU64 !arr !i !j = do
  ok <- aSwapF64 arr i j
  if ok then return arr else aSwapU arr i j
{-# INLINE aSwapU64 #-}

aSwapFW :: Arr -> Int -> Int -> IO Bool
aSwapFW !arr !i !j
  | outOfRange i arr || outOfRange j arr = return True
  | otherwise = do
      node <- readIORef (aRef arr)
      case node of
        Direct (BW a) c | c >= 0 -> do
          x <- unsafeRead a i
          y <- unsafeRead a j
          unsafeWrite a i y
          unsafeWrite a j x
          return True
        _ -> return False
{-# INLINE aSwapFW #-}

aSwapUW :: Arr -> Int -> Int -> IO Arr
aSwapUW !arr !i !j = do
  ok <- aSwapFW arr i j
  if ok then return arr else aSwapU arr i j
{-# INLINE aSwapUW #-}

-- | The read for every case the inline narrow ones do not handle (a boxed buffer, an old version, a lazy
-- handle). @kind@ is the element width: 8, 16, 32 or 64. The default arrives boxed and is not forced unless used.
getPN :: Int -> Arr -> Int -> Any -> State# RealWorld -> (# State# RealWorld, Word# #)
getPN kind arr i d s
  | outOfRange i arr = case widenAny kind d of W# w -> (# s, w #)
  | otherwise = case readIORef (aRef arr) of
      IO m -> case m s of
        (# s1, node #) -> case node of
          Direct buf _ -> readBuf buf s1
          Lazy src -> getPN kind src i d s1
          _ -> case reroot arr of
            IO m2 -> case m2 s1 of (# s2, buf #) -> readBuf buf s2
  where
    readBuf buf st = case bufRead buf i of
      IO r -> case r st of (# st', v #) -> case widenAny kind v of W# w -> (# st', w #)
{-# NOINLINE getPN #-}

widenAny :: Int -> Any -> Word
widenAny kind v = case kind of
  8 -> fromIntegral (unsafeCoerce v :: Word8)
  16 -> fromIntegral (unsafeCoerce v :: Word16)
  32 -> fromIntegral (unsafeCoerce v :: Word32)
  _ -> fromIntegral (unsafeCoerce v :: Word64)

-- * Moving an element between arrays

-- | Copy element @j@ of one buffer to slot @i@ of another. Two buffers of the same kind exchange the
-- raw element, so a `Word` or `Word8` is never boxed on the way.
bufCopy :: Buf -> Int -> Buf -> Int -> IO ()
bufCopy d i s j = case d of
  BBox a | BBox b <- s -> mv a b
  BW a | BW b <- s -> mv a b
  B8 a | B8 b <- s -> mv a b
  B16 a | B16 b <- s -> mv a b
  B32 a | B32 b <- s -> mv a b
  B64 a | B64 b <- s -> mv a b
  BBool a | BBool b <- s -> mv a b
  _ -> bufRead s j >>= bufWrite d i
  where
    mv :: (MArray a e IO) => a Int e -> a Int e -> IO ()
    mv a b = unsafeRead b j >>= unsafeWrite a i
    {-# INLINE mv #-}

-- | `aPushU` of element @i@ of another array, moved without boxing (what `Array.append` and
-- `Array.extract` do for each element). An index out of range is the same error as `aGet`'s.
aPushFromU :: Arr -> Arr -> Int -> IO Arr
aPushFromU arr src i = do
  node <- ownNode arr
  snode <- readIORef (aRef src)
  case (node, snode) of
    (Direct buf c, Direct sbuf _) | c >= 0 && i >= 0 && i < aLen src -> do
      cap <- bufCap buf
      let n = aLen arr
      if n < cap
        then bufCopy buf n sbuf i
        else do
          b <- bufGrow buf n (max 4 (2 * cap))
          bufCopy b n sbuf i
          writeIORef (aRef arr) (Direct b c)
      return (Arr (n + 1) (aRef arr))
    _ -> aGet src i (error "leanzempic: array index out of range") >>= aPushU arr

-- * Hoisted buffers
--
-- A loop over an array that the ownership analysis proved unshared, and that only reads it and swaps or
-- overwrites elements in place, need not look at the array's node on every access: the node cannot change
-- while the loop runs (nothing else holds the array, and the loop never pushes, pops, copies or hands it
-- on). The array may be a parameter of the loop or lie inside the loop-state cells that a @for@ or @while@
-- loop passes around. The emitter resolves the buffer once, at the loop's entry, with 'aHoist8' .. 'aHoist64',
-- 'aHoistW' (a @Word@ buffer: @USize@, or @Nat@ in word mode) or 'aHoistBool', and the loop then reads and
-- writes the raw buffer through 'hGetD', 'hGetBool', 'hSwap' and 'hSet'. If the array is not in the one
-- state the loop needs (a live buffer of the right kind, not marked stale, not a lazy handle), the loop runs
-- on the ordinary primitives instead, and re-checks at each step, so a lazy handle that its first write turns
-- into a live buffer is picked up from the next step on.

-- | A live buffer of element type @e@ and the array's length, resolved once.
data HB e = HB {-# UNPACK #-} !Int {-# UNPACK #-} !(IOUArray Int e)

-- | Run @ok@ with the raw buffer if this array is a live (not stale, not lazy) buffer of kind 'B32'
-- (resp. 8, 16, 64); otherwise run @slow@.
aHoist32 :: Arr -> (HB Word32 -> r) -> r -> r
aHoist32 arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (B32 a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoist32 #-}

aHoist8 :: Arr -> (HB Word8 -> r) -> r -> r
aHoist8 arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (B8 a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoist8 #-}

aHoist16 :: Arr -> (HB Word16 -> r) -> r -> r
aHoist16 arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (B16 a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoist16 #-}

aHoist64 :: Arr -> (HB Word64 -> r) -> r -> r
aHoist64 arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (B64 a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoist64 #-}

-- | The same for a 'BW' buffer (a @Word@ array: @USize@, or @Nat@ in word mode).
aHoistW :: Arr -> (HB Word -> r) -> r -> r
aHoistW arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (BW a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoistW #-}

-- | The same for a 'BBool' buffer (one byte per element, 0 or 1).
aHoistBool :: Arr -> (HB Word8 -> r) -> r -> r
aHoistBool arr ok slow = case unsafeDupablePerformIO (readIORef (aRef arr)) of
  Direct (BBool a) c | c >= 0 -> ok (HB (aLen arr) a)
  _ -> slow
{-# INLINE aHoistBool #-}

-- | Read element @i@ of a hoisted buffer: the default when out of range (not forced otherwise); one unsigned
-- comparison. One function per width, written on the primitive read so that no box is built for the result.
hGetD8 :: HB Word8 -> Int -> Word8 -> Word8
hGetD8 (HB n (IOUArray (STUArray _ _ _ m))) i@(I# i#) d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = case runRW# (readWord8Array# m i#) of (# _, w #) -> W8# w
{-# INLINE hGetD8 #-}

hGetD16 :: HB Word16 -> Int -> Word16 -> Word16
hGetD16 (HB n (IOUArray (STUArray _ _ _ m))) i@(I# i#) d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = case runRW# (readWord16Array# m i#) of (# _, w #) -> W16# w
{-# INLINE hGetD16 #-}

hGetD32 :: HB Word32 -> Int -> Word32 -> Word32
hGetD32 (HB n (IOUArray (STUArray _ _ _ m))) i@(I# i#) d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = case runRW# (readWord32Array# m i#) of (# _, w #) -> W32# w
{-# INLINE hGetD32 #-}

hGetD64 :: HB Word64 -> Int -> Word64 -> Word64
hGetD64 (HB n (IOUArray (STUArray _ _ _ m))) i@(I# i#) d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = case runRW# (readWord64Array# m i#) of (# _, w #) -> W64# w
{-# INLINE hGetD64 #-}

hGetDW :: HB Word -> Int -> Word -> Word
hGetDW (HB n (IOUArray (STUArray _ _ _ m))) i@(I# i#) d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = case runRW# (readWordArray# m i#) of (# _, w #) -> W# w
{-# INLINE hGetDW #-}

-- | Read element @i@ of a hoisted 'BBool' buffer as a boxed @Bool@ (the default, already boxed, when out of range).
hGetBool :: HB Word8 -> Int -> Any -> Any
hGetBool b@(HB n _) i d
  | (fromIntegral i :: Word) >= fromIntegral n = d
  | otherwise = unsafeCoerce (hGetD8 b i 0 /= 0)
{-# INLINE hGetBool #-}

-- | Exchange two elements in place (out of range: nothing happens); returns the array it was given.
hSwap :: MArray IOUArray e IO => HB e -> x -> Int -> Int -> x
hSwap (HB n a) arr i j
  | (fromIntegral i :: Word) >= fromIntegral n || (fromIntegral j :: Word) >= fromIntegral n = arr
  | otherwise = unsafeDupablePerformIO (do
      x <- unsafeRead a i
      y <- unsafeRead a j
      unsafeWrite a i y
      unsafeWrite a j x
      return arr)
{-# INLINE hSwap #-}

-- | Overwrite an element in place (out of range: nothing happens); returns the array it was given.
hSet :: MArray IOUArray e IO => HB e -> x -> Int -> e -> x
hSet (HB n a) arr i v
  | (fromIntegral i :: Word) >= fromIntegral n = arr
  | otherwise = unsafeDupablePerformIO (unsafeWrite a i v >> return arr)
{-# INLINE hSet #-}
