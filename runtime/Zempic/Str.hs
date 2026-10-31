{-# LANGUAGE BangPatterns, MagicHash, UnboxedTuples #-}
-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's String as a UTF-8 byte buffer shared by all versions of a string.
--
-- Strings are only ever appended to, so every version is a prefix of one buffer and a prefix
-- never changes. Appending to the newest version (the usual loop) writes in place after the end
-- of the data, amortized O(1). Appending to an older version copies, so no version can ever see
-- bytes it did not write. Lean gets the same speed from reference counts; this needs none.
--
-- Buffer layout: an unpinned mutable byte array holding an 8-byte count of how many data bytes any
-- version has written, then the data. Keeping the count in the buffer, not in a separate mutable
-- cell, keeps appends allocation-light, and an unpinned array is allocated by bumping the nursery
-- pointer (a pinned one goes through the block allocator, several times the instructions). Bytes
-- below a version's length never change, so reading them is a pure operation.
module Zempic.Str
  ( Str, sFromText, sFromIntegral, sFromWord, sToText, sBytes, sChars, sAppend, sPush, sEq, sLt, sLe
  , sByteAt, sCharAt, sCharWidthAt, sCharAtW, sCharWidthAtW, sExtract, sPushn, sPushByte, sSetByte, sPrev, sHash, sMemEq
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import qualified Data.ByteString.Unsafe as BU
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word64, Word8)
import GHC.Exts
  ( Int (..), MutableByteArray#, RealWorld, Ptr (..), copyAddrToByteArray#, copyMutableByteArray#
  , copyMutableByteArrayToAddr#, compareByteArrays#, indexWord8Array#, newByteArray#, readIntArray#
  , sizeofMutableByteArray#, unsafeCoerce#, writeIntArray#, writeWord8Array#, (+#), (-#) )
import GHC.IO (IO (..))
import GHC.Word (Word8 (..))

-- | A mutable byte array (boxed so it can be passed to closures and returned from IO).
data MBA = MBA (MutableByteArray# RealWorld)

-- | A buffer (its data capacity is its size minus the header), this version's byte length, and its
-- length in characters.
data Str = Str (MutableByteArray# RealWorld) !Int !Int

sBytes, sChars :: Str -> Int
sBytes (Str _ n _) = n
sChars (Str _ _ c) = c

hdr :: Int
hdr = 8

-- | A buffer with room for @want@ data bytes (at least 16) and a zero count.
newBuf :: Int -> IO MBA
newBuf want = IO $ \s -> case max 16 want + hdr of
  I# sz -> case newByteArray# sz s of
    (# s1, a #) -> case writeIntArray# a 0# 0# s1 of s2 -> (# s2, MBA a #)

capOf :: MutableByteArray# RealWorld -> Int
capOf a = I# (sizeofMutableByteArray# a -# 8#)
{-# INLINE capOf #-}

getCount :: MutableByteArray# RealWorld -> IO Int
getCount a = IO $ \s -> case readIntArray# a 0# s of (# s1, x #) -> (# s1, I# x #)
{-# INLINE getCount #-}

setCount :: MutableByteArray# RealWorld -> Int -> IO ()
setCount a (I# n) = IO $ \s -> case writeIntArray# a 0# n s of s1 -> (# s1, () #)
{-# INLINE setCount #-}

-- | Write data byte @i@ (the caller guarantees room).
wr8 :: MutableByteArray# RealWorld -> Int -> Word8 -> IO ()
wr8 a (I# i) (W8# w) = IO $ \s -> case writeWord8Array# a (i +# 8#) w s of s1 -> (# s1, () #)
{-# INLINE wr8 #-}

-- | Copy @n@ data bytes from offset @so@ of one buffer to offset @do'@ of another.
copyData :: MutableByteArray# RealWorld -> Int -> MutableByteArray# RealWorld -> Int -> Int -> IO ()
copyData src (I# so) dst (I# d) (I# n) =
  IO $ \s -> case copyMutableByteArray# src (so +# 8#) dst (d +# 8#) n s of s1 -> (# s1, () #)
{-# INLINE copyData #-}

-- | Data byte @i@ of a buffer. Bytes below a version's length never change, so this is pure.
byteOf :: MutableByteArray# RealWorld -> Int -> Word8
byteOf a (I# i) = W8# (indexWord8Array# (unsafeCoerce# a) (i +# 8#))
{-# INLINE byteOf #-}

sFromText :: T.Text -> IO Str
sFromText t = do
  let bs = TE.encodeUtf8 t
      n = B.length bs
  MBA a <- newBuf n
  BU.unsafeUseAsCString bs $ \(Ptr src) -> case n of
    I# n# -> IO $ \s -> case copyAddrToByteArray# src a 8# n# s of s1 -> (# s1, () #)
  setCount a n
  return (Str a n (T.length t))

-- | The decimal digits of a non-negative number, written straight into a fresh buffer.
sFromIntegral :: Integral a => a -> IO Str
sFromIntegral n0 = do
  let digits = countDigits n0 :: Int
  MBA a <- newBuf digits
  let go i n
        | i < 0 = return ()
        | otherwise = do
            let (q, r) = n `quotRem` 10
            wr8 a i (fromIntegral r + 48)
            go (i - 1) q
  go (digits - 1) n0
  setCount a digits
  return (Str a digits digits)
{-# INLINABLE sFromIntegral #-}

-- | 'sFromIntegral' for a machine word: the digit count comes from comparisons, not divisions.
sFromWord :: Word -> IO Str
sFromWord n0 = do
  let digits = wordDigits n0
  MBA a <- newBuf digits
  let go !i !n
        | i < 0 = return ()
        | otherwise = do
            let (q, r) = n `quotRem` 10
            wr8 a i (fromIntegral r + 48)
            go (i - 1) q
  go (digits - 1) n0
  setCount a digits
  return (Str a digits digits)

wordDigits :: Word -> Int
wordDigits n = go 1 10
  where go !d !p | n < p = d
                 | d == 20 = 20
                 | otherwise = go (d + 1) (p * 10)
{-# INLINE wordDigits #-}

countDigits :: Integral a => a -> Int
countDigits n = if n < 10 then 1 else 1 + countDigits (n `quot` 10)
{-# INLINABLE countDigits #-}

sToText :: Str -> T.Text
sToText (Str a n@(I# n#) _) = TE.decodeUtf8 (BI.unsafeCreate n $ \(Ptr p) ->
  IO $ \s -> case copyMutableByteArrayToAddr# a 8# p n# s of s1 -> (# s1, () #))

-- | Add @k@ bytes (@kc@ characters) written by @writer@ (given the buffer and the offset of the first
-- new byte) to the end of a version.
{-# INLINE appendWith #-}
appendWith :: Str -> Int -> Int -> (MutableByteArray# RealWorld -> Int -> IO ()) -> IO Str
appendWith (Str a n c) k kc writer = do
  u <- getCount a
  if u == n && n + k <= capOf a
    then do
      writer a n
      setCount a (n + k)
      return (Str a (n + k) (c + kc))
    else do
      MBA a' <- newBuf (max (n + k) (2 * n))
      copyData a 0 a' 0 n
      writer a' n
      setCount a' (n + k)
      return (Str a' (n + k) (c + kc))

sAppend :: Str -> Str -> IO Str
sAppend a (Str b bn bc)
  | bn == 0 = return a
  | otherwise = appendWith a bn bc $ \dst off -> copyData b 0 dst off bn

-- | Append one character given as a code point.
sPush :: Str -> Word32 -> IO Str
sPush s@(Str a n c) w
  | w < 0x80 = do
      -- The common case, kept free of closures: one byte onto the newest version.
      u <- getCount a
      if u == n && n < capOf a
        then do
          wr8 a n (fromIntegral w)
          setCount a (n + 1)
          return (Str a (n + 1) (c + 1))
        else pushSlow s w
  | otherwise = pushSlow s w

pushSlow :: Str -> Word32 -> IO Str
pushSlow s c
  | c < 0x80 = appendWith s 1 1 $ \p o -> wr8 p o (fromIntegral c)
  | c < 0x800 = appendWith s 2 1 $ \p o -> do
      wr8 p o (fromIntegral (0xC0 .|. (c `shiftR` 6)))
      wr8 p (o + 1) (fromIntegral (0x80 .|. (c .&. 0x3F)))
  | c < 0x10000 = appendWith s 3 1 $ \p o -> do
      wr8 p o (fromIntegral (0xE0 .|. (c `shiftR` 12)))
      wr8 p (o + 1) (fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)))
      wr8 p (o + 2) (fromIntegral (0x80 .|. (c .&. 0x3F)))
  | otherwise = appendWith s 4 1 $ \p o -> do
      wr8 p o (fromIntegral (0xF0 .|. (c `shiftR` 18)))
      wr8 p (o + 1) (fromIntegral (0x80 .|. ((c `shiftR` 12) .&. 0x3F)))
      wr8 p (o + 2) (fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)))
      wr8 p (o + 3) (fromIntegral (0x80 .|. (c .&. 0x3F)))

-- | Compare the bytes of two strings; UTF-8 byte order is code point order.
cmp :: Str -> Str -> Ordering
cmp (Str a na _) (Str b nb _) = case min na nb of
  I# m -> case compare (I# (compareByteArrays# (unsafeCoerce# a) 8# (unsafeCoerce# b) 8# m)) 0 of
    EQ -> compare na nb
    o -> o

sEq, sLt, sLe :: Str -> Str -> Bool
sEq a@(Str _ na _) b@(Str _ nb _) = na == nb && cmp a b == EQ
sLt a b = cmp a b == LT
sLe a b = cmp a b /= GT

-- | Byte @i@ of the data (the caller checks @i < sBytes@).
sByteAt :: Str -> Int -> Word8
sByteAt (Str a _ _) i = byteOf a i
{-# INLINE sByteAt #-}

-- | Width in bytes of the character whose first byte is @b@.
widthOf :: Word8 -> Int
widthOf b
  | b < 0x80 = 1
  | b < 0xE0 = if b >= 0xC0 then 2 else 1
  | b < 0xF0 = 3
  | b < 0xF8 = 4
  | otherwise = 1
{-# INLINE widthOf #-}

-- | Width in bytes of the character whose first byte is at @i@ (1 when @i@ is past the end, as
-- Lean's @next@ treats the default character).
sCharWidthAt :: Str -> Int -> Int
sCharWidthAt (Str a n _) i
  | i < 0 || i >= n = 1
  | otherwise = widthOf (byteOf a i)
{-# INLINE sCharWidthAt #-}

-- | The character starting at byte @i@, or Lean's default character @A@ outside the string. The
-- ASCII case is one inlined read; the rest is straight-line code with no call, so the loop around
-- it keeps its values in registers.
sCharAt :: Str -> Int -> Word32
sCharAt s@(Str a n _) i
  | i < 0 || i >= n = 65
  | otherwise =
      let b0 = byteOf a i
      in if b0 < 0x80 then fromIntegral b0 else multiByte s i b0
{-# INLINE sCharAt #-}

multiByte :: Str -> Int -> Word8 -> Word32
multiByte (Str a n _) !i !b0 =
  if b0 .&. 0xC0 == 0x80 then 65  -- inside a character: Lean's @get@ answers the default character
  else case widthOf b0 of
    2 -> (fromIntegral (b0 .&. 0x1F) * 64) .|. cont 1
    3 -> (fromIntegral (b0 .&. 0x0F) * 4096) .|. (cont 1 * 64) .|. cont 2
    4 -> (fromIntegral (b0 .&. 0x07) * 262144) .|. (cont 1 * 4096) .|. (cont 2 * 64) .|. cont 3
    _ -> fromIntegral b0
  where
    cont :: Int -> Word32
    cont k = if i + k < n then fromIntegral (byteOf a (i + k) .&. 0x3F) else 0
{-# INLINE multiByte #-}

-- | 'sCharAt' for an unsigned position: one unsigned compare covers both ends of the range.
sCharAtW :: Str -> Word -> Word32
sCharAtW s@(Str a n _) w
  | w >= fromIntegral n = 65
  | otherwise =
      let i = fromIntegral w :: Int
          b0 = byteOf a i
      in if b0 < 0x80 then fromIntegral b0 else multiByte s i b0
{-# INLINE sCharAtW #-}

-- | 'sCharWidthAt' for an unsigned position.
sCharWidthAtW :: Str -> Word -> Int
sCharWidthAtW (Str a n _) w
  | w >= fromIntegral n = 1
  | otherwise = widthOf (byteOf a (fromIntegral w))
{-# INLINE sCharWidthAtW #-}

-- | The start of the character before byte @i@ (0 at the start), as Lean's @prev@.
sPrev :: Str -> Int -> Int
sPrev s@(Str _ n _) i
  | i <= 0 = 0
  | i > n = i - 1  -- past the end Lean answers @i - 1@
  | otherwise = go (min i n - 1)
  where go j | j <= 0 = 0
             | sByteAt s j .&. 0xC0 /= 0x80 = j
             | otherwise = go (j - 1)

-- | Bytes @[b, e)@ as a new string, with Lean's rules: empty if @b >= e@, @b@ past the end or @b@
-- inside a character; an @e@ inside a character means the end of the string.
sExtract :: Str -> Int -> Int -> IO Str
sExtract s@(Str a n _) b e0
  | b >= e0 || b >= n || b < 0 || sByteAt s b .&. 0xC0 == 0x80 = sFromText T.empty
  | otherwise = do
      let e1 = min e0 n
          e = if e1 < n && sByteAt s e1 .&. 0xC0 == 0x80 then n else e1
          k = e - b
          chars = length [() | j <- [b .. e - 1], sByteAt s j .&. 0xC0 /= 0x80]
      MBA a' <- newBuf k
      copyData a b a' 0 k
      setCount a' k
      return (Str a' k chars)

-- | Append a character @k@ times.
sPushn :: Str -> Word32 -> Int -> IO Str
sPushn s c k
  | k <= 0 = return s
  | otherwise = sPush s c >>= \s' -> sPushn s' c (k - 1)

-- | Append one raw byte (a ByteArray push). The character count is not meaningful for byte arrays.
sPushByte :: Str -> Word8 -> IO Str
sPushByte s b = appendWith s 1 0 $ \p o -> wr8 p o b

-- | A copy with byte @i@ replaced (a ByteArray set); out-of-range leaves the array unchanged.
sSetByte :: Str -> Int -> Word8 -> IO Str
sSetByte s@(Str a n c) i b
  | i < 0 || i >= n = return s
  | otherwise = do
      MBA a' <- newBuf n
      copyData a 0 a' 0 n
      wr8 a' i b
      setCount a' n
      return (Str a' n c)

-- | Lean's string hash: MurmurHash64A of the UTF-8 bytes with seed 11. Must match exactly, since
-- hash maps iterate in hash order.
sHash :: Str -> Word64
sHash s@(Str _ n _) = finish (tailMix (blocks (11 `xor` (fromIntegral n * m)) 0))
  where
    m = 0xc6a4a7935bd1e995 :: Word64
    word64At i = foldr (\j acc -> acc * 256 + fromIntegral (sByteAt s (i + j))) 0 [0 .. 7] :: Word64
    blocks h i
      | i + 8 <= n =
          let k0 = word64At i * m
              k1 = k0 `xor` (k0 `shiftR` 47)
              k2 = k1 * m
          in blocks ((h `xor` k2) * m) (i + 8)
      | otherwise = (h, i)
    tailMix (h, i)
      | n - i == 0 = h
      | otherwise =
          let h' = foldl (\acc j -> acc `xor` (fromIntegral (sByteAt s (i + j)) `shiftL` (8 * j))) h [0 .. n - i - 1]
          in h' * m
    finish h0 = let h1 = h0 `xor` (h0 `shiftR` 47); h2 = h1 * m in h2 `xor` (h2 `shiftR` 47)

-- | Do @len@ bytes of @a@ from @i@ equal @len@ bytes of @b@ from @j@?
sMemEq :: Str -> Str -> Int -> Int -> Int -> Bool
sMemEq a b i j len = all (\k -> sByteAt a (i + k) == sByteAt b (j + k)) [0 .. len - 1]
