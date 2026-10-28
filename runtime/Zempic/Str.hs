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
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import qualified Data.ByteString.Unsafe as BU
import Data.Bits (shiftR, (.&.), (.|.))
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word8)
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrBytes)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peek, poke, pokeByteOff)
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
