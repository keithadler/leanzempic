-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's String as a UTF-8 byte buffer shared by all versions of a string.
--
-- Strings are only ever appended to, so every version is a prefix of one buffer and a prefix
-- never changes. Appending to the newest version (the usual loop) writes in place after the end
-- of the data, amortized O(1). Appending to an older version copies, so no version can ever see
-- bytes it did not write. Lean gets the same speed from reference counts; this needs none.
--
-- Buffer layout: an 8-byte count of how many data bytes any version has written, then the data.
-- Keeping the count in the buffer, not in a separate mutable cell, keeps appends allocation-light.
module Zempic.Str
  ( Str, sFromText, sFromIntegral, sToText, sBytes, sChars, sAppend, sPush, sEq, sLt, sLe
  , sByteAt, sCharAt, sCharWidthAt, sExtract, sPushn, sPushByte, sSetByte, sPrev, sHash, sMemEq
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import qualified Data.ByteString.Unsafe as BU
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word64, Word8)
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrBytes)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peek, peekByteOff, poke, pokeByteOff)
import GHC.ForeignPtr (unsafeWithForeignPtr)
import System.IO.Unsafe (unsafeDupablePerformIO)

foreign import ccall unsafe "string.h memcmp"
  c_memcmp :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt

-- | A buffer and its data capacity.
data Buf = Buf !(ForeignPtr Word8) !Int

-- | A buffer, this version's byte length, and its length in characters.
data Str = Str !Buf !Int !Int

sBytes, sChars :: Str -> Int
sBytes (Str _ n _) = n
sChars (Str _ _ c) = c

hdr :: Int
hdr = 8

newBuf :: Int -> IO Buf
newBuf want = do
  let cap = max 16 want
  fp <- mallocForeignPtrBytes (cap + hdr)
  unsafeWithForeignPtr fp $ \p -> poke (castPtr p :: Ptr Int) 0
  return (Buf fp cap)

sFromText :: T.Text -> IO Str
sFromText t = do
  let bs = TE.encodeUtf8 t
      n = B.length bs
  buf@(Buf fp _) <- newBuf n
  unsafeWithForeignPtr fp $ \p -> do
    BU.unsafeUseAsCString bs $ \src -> copyBytes (p `plusPtr` hdr) (castPtr src) n
    poke (castPtr p :: Ptr Int) n
  return (Str buf n (T.length t))

-- | The decimal digits of a non-negative number, written straight into a fresh buffer.
sFromIntegral :: Integral a => a -> IO Str
sFromIntegral n0 = do
  let digits = countDigits n0 :: Int
  buf@(Buf fp _) <- newBuf digits
  unsafeWithForeignPtr fp $ \p -> do
    let go i n
          | i < 0 = return ()
          | otherwise = do
              let (q, r) = n `quotRem` 10
              pokeByteOff p (hdr + i) (fromIntegral r + 48 :: Word8)
              go (i - 1) q
    go (digits - 1) n0
    poke (castPtr p :: Ptr Int) digits
  return (Str buf digits digits)
{-# INLINABLE sFromIntegral #-}

countDigits :: Integral a => a -> Int
countDigits n = if n < 10 then 1 else 1 + countDigits (n `quot` 10)
{-# INLINABLE countDigits #-}

sToText :: Str -> T.Text
sToText (Str (Buf fp _) n _) = TE.decodeUtf8 (BI.fromForeignPtr (castForeign fp hdr) 0 n)
  where castForeign f off = BI.plusForeignPtr f off

-- | Add @k@ bytes (@kc@ characters) written by @writer@ to the end of a version.
appendWith :: Str -> Int -> Int -> (Ptr Word8 -> IO ()) -> IO Str
appendWith (Str buf@(Buf fp cap) n c) k kc writer = do
  u <- unsafeWithForeignPtr fp $ \p -> peek (castPtr p :: Ptr Int)
  if u == n && n + k <= cap
    then do
      unsafeWithForeignPtr fp $ \p -> do
        writer (p `plusPtr` (hdr + n))
        poke (castPtr p :: Ptr Int) (n + k)
      return (Str buf (n + k) (c + kc))
    else do
      buf'@(Buf fp' _) <- newBuf (max (n + k) (2 * n))
      unsafeWithForeignPtr fp $ \src -> unsafeWithForeignPtr fp' $ \dst -> do
        copyBytes (dst `plusPtr` hdr) (src `plusPtr` hdr) n
        writer (dst `plusPtr` (hdr + n))
        poke (castPtr dst :: Ptr Int) (n + k)
      return (Str buf' (n + k) (c + kc))

sAppend :: Str -> Str -> IO Str
sAppend a (Str (Buf bfp _) bn bc)
  | bn == 0 = return a
  | otherwise = appendWith a bn bc $ \dst ->
      unsafeWithForeignPtr bfp $ \src -> copyBytes dst (src `plusPtr` hdr) bn

-- | Append one character given as a code point.
sPush :: Str -> Word32 -> IO Str
sPush s@(Str buf@(Buf fp cap) n c) w
  | w < 0x80 =
      -- The common case, kept free of closures: one byte onto the newest version.
      unsafeWithForeignPtr fp $ \p -> do
        u <- peek (castPtr p :: Ptr Int)
        if u == n && n < cap
          then do
            pokeByteOff p (hdr + n) (fromIntegral w :: Word8)
            poke (castPtr p :: Ptr Int) (n + 1)
            return (Str buf (n + 1) (c + 1))
          else pushSlow s w
  | otherwise = pushSlow s w

pushSlow :: Str -> Word32 -> IO Str
pushSlow s c
  | c < 0x80 = appendWith s 1 1 $ \p -> pokeByteOff p 0 (fromIntegral c :: Word8)
  | c < 0x800 = appendWith s 2 1 $ \p -> do
      pokeByteOff p 0 (fromIntegral (0xC0 .|. (c `shiftR` 6)) :: Word8)
      pokeByteOff p 1 (fromIntegral (0x80 .|. (c .&. 0x3F)) :: Word8)
  | c < 0x10000 = appendWith s 3 1 $ \p -> do
      pokeByteOff p 0 (fromIntegral (0xE0 .|. (c `shiftR` 12)) :: Word8)
      pokeByteOff p 1 (fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)) :: Word8)
      pokeByteOff p 2 (fromIntegral (0x80 .|. (c .&. 0x3F)) :: Word8)
  | otherwise = appendWith s 4 1 $ \p -> do
      pokeByteOff p 0 (fromIntegral (0xF0 .|. (c `shiftR` 18)) :: Word8)
      pokeByteOff p 1 (fromIntegral (0x80 .|. ((c `shiftR` 12) .&. 0x3F)) :: Word8)
      pokeByteOff p 2 (fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)) :: Word8)
      pokeByteOff p 3 (fromIntegral (0x80 .|. (c .&. 0x3F)) :: Word8)

-- | Compare the bytes of two strings; UTF-8 byte order is code point order.
cmp :: Str -> Str -> Ordering
cmp (Str (Buf fa _) na _) (Str (Buf fb _) nb _) = unsafeDupablePerformIO $
  unsafeWithForeignPtr fa $ \pa -> unsafeWithForeignPtr fb $ \pb -> do
    r <- c_memcmp (pa `plusPtr` hdr) (pb `plusPtr` hdr) (fromIntegral (min na nb))
    return $ case compare r 0 of
      EQ -> compare na nb
      o -> o

sEq, sLt, sLe :: Str -> Str -> Bool
sEq a@(Str _ na _) b@(Str _ nb _) = na == nb && cmp a b == EQ
sLt a b = cmp a b == LT
sLe a b = cmp a b /= GT

-- | Byte @i@ of the data (the caller checks @i < sBytes@).
sByteAt :: Str -> Int -> Word8
sByteAt (Str (Buf fp _) _ _) i = unsafeDupablePerformIO $
  unsafeWithForeignPtr fp $ \p -> peekByteOff p (hdr + i)
{-# INLINE sByteAt #-}

-- | Width in bytes of the character whose first byte is at @i@ (1 when @i@ is past the end, as
-- Lean's @next@ treats the default character).
sCharWidthAt :: Str -> Int -> Int
sCharWidthAt s@(Str _ n _) i
  | i < 0 || i >= n = 1
  | b < 0x80 = 1
  | b .&. 0xE0 == 0xC0 = 2
  | b .&. 0xF0 == 0xE0 = 3
  | b .&. 0xF8 == 0xF0 = 4
  | otherwise = 1
  where b = sByteAt s i

-- | The character starting at byte @i@, or Lean's default character @A@ outside the string.
sCharAt :: Str -> Int -> Word32
sCharAt s@(Str _ n _) i
  | i < 0 || i >= n = 65
  | otherwise = case sCharWidthAt s i of
      1 -> fromIntegral b0
      2 -> (fromIntegral (b0 .&. 0x1F) * 64) .|. cont 1
      3 -> (fromIntegral (b0 .&. 0x0F) * 4096) .|. (cont 1 * 64) .|. cont 2
      _ -> (fromIntegral (b0 .&. 0x07) * 262144) .|. (cont 1 * 4096) .|. (cont 2 * 64) .|. cont 3
  where
    b0 = sByteAt s i
    cont k = if i + k < n then fromIntegral (sByteAt s (i + k) .&. 0x3F) else 0 :: Word32

-- | The start of the character before byte @i@ (0 at the start), as Lean's @prev@.
sPrev :: Str -> Int -> Int
sPrev s@(Str _ n _) i
  | i <= 0 = 0
  | otherwise = go (min i n - 1)
  where go j | j <= 0 = 0
             | sByteAt s j .&. 0xC0 /= 0x80 = j
             | otherwise = go (j - 1)

-- | Bytes @[b, e)@ as a new string, with Lean's rules: empty if @b >= e@, @b@ past the end or @b@
-- inside a character; an @e@ inside a character means the end of the string.
sExtract :: Str -> Int -> Int -> IO Str
sExtract s@(Str (Buf fp _) n _) b e0
  | b >= e0 || b >= n || b < 0 || sByteAt s b .&. 0xC0 == 0x80 = sFromText T.empty
  | otherwise = do
      let e1 = min e0 n
          e = if e1 < n && sByteAt s e1 .&. 0xC0 == 0x80 then n else e1
          k = e - b
          chars = length [() | j <- [b .. e - 1], sByteAt s j .&. 0xC0 /= 0x80]
      buf'@(Buf fp' _) <- newBuf k
      unsafeWithForeignPtr fp $ \src -> unsafeWithForeignPtr fp' $ \dst -> do
        copyBytes (dst `plusPtr` hdr) (src `plusPtr` (hdr + b)) k
        poke (castPtr dst :: Ptr Int) k
      return (Str buf' k chars)

-- | Append a character @k@ times.
sPushn :: Str -> Word32 -> Int -> IO Str
sPushn s c k
  | k <= 0 = return s
  | otherwise = sPush s c >>= \s' -> sPushn s' c (k - 1)

-- | Append one raw byte (a ByteArray push). The character count is not meaningful for byte arrays.
sPushByte :: Str -> Word8 -> IO Str
sPushByte s b = appendWith s 1 0 $ \p -> pokeByteOff p 0 b

-- | A copy with byte @i@ replaced (a ByteArray set); out-of-range leaves the array unchanged.
sSetByte :: Str -> Int -> Word8 -> IO Str
sSetByte s@(Str (Buf fp _) n c) i b
  | i < 0 || i >= n = return s
  | otherwise = do
      buf'@(Buf fp' _) <- newBuf n
      unsafeWithForeignPtr fp $ \src -> unsafeWithForeignPtr fp' $ \dst -> do
        copyBytes (dst `plusPtr` hdr) (src `plusPtr` hdr) n
        pokeByteOff dst (hdr + i) b
        poke (castPtr dst :: Ptr Int) n
      return (Str buf' n c)

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
