-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Lean's String as a UTF-8 byte buffer shared by all versions of a string.
--
-- Strings are only ever appended to, so every version is a prefix of one buffer and a prefix
-- never changes. Appending to the newest version (the usual loop) writes in place after the end
-- of the data, amortized O(1). Appending to an older version copies, so no version can ever see
-- bytes it did not write. Lean gets the same speed from reference counts; this needs none.
module Zempic.Str
  ( Str, sFromText, sToText, sBytes, sChars, sAppend, sPush, sEq, sLt, sLe
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import qualified Data.ByteString.Unsafe as BU
import Data.Bits (shiftR, (.&.), (.|.))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word32, Word8)
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrBytes, withForeignPtr)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (pokeByteOff)
import System.IO.Unsafe (unsafeDupablePerformIO)

foreign import ccall unsafe "string.h memcmp"
  c_memcmp :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt

-- | A buffer, its capacity, and how many bytes any version has written so far.
data Buf = Buf !(ForeignPtr Word8) !Int !(IORef Int)

-- | A buffer, this version's byte length, and its length in characters.
data Str = Str !Buf !Int !Int

sBytes, sChars :: Str -> Int
sBytes (Str _ n _) = n
sChars (Str _ _ c) = c

newBuf :: Int -> IO Buf
newBuf want = do
  let cap = max 16 want
  fp <- mallocForeignPtrBytes cap
  Buf fp cap <$> newIORef 0

sFromText :: T.Text -> IO Str
sFromText t = do
  let bs = TE.encodeUtf8 t
      n = B.length bs
  buf@(Buf fp _ used) <- newBuf n
  withForeignPtr fp $ \p -> BU.unsafeUseAsCString bs $ \src -> copyBytes p (castPtr src) n
  writeIORef used n
  return (Str buf n (T.length t))

sToText :: Str -> T.Text
sToText (Str (Buf fp _ _) n _) = TE.decodeUtf8 (BI.fromForeignPtr fp 0 n)

-- | Add @k@ bytes (@kc@ characters) written by @writer@ to the end of a version.
appendWith :: Str -> Int -> Int -> (Ptr Word8 -> IO ()) -> IO Str
appendWith (Str buf@(Buf fp cap used) n c) k kc writer = do
  u <- readIORef used
  if u == n && n + k <= cap
    then do
      withForeignPtr fp $ \p -> writer (p `plusPtr` n)
      writeIORef used (n + k)
      return (Str buf (n + k) (c + kc))
    else do
      buf'@(Buf fp' _ used') <- newBuf (max (n + k) (2 * n))
      withForeignPtr fp $ \src -> withForeignPtr fp' $ \dst -> do
        copyBytes dst src n
        writer (dst `plusPtr` n)
      writeIORef used' (n + k)
      return (Str buf' (n + k) (c + kc))

sAppend :: Str -> Str -> IO Str
sAppend a (Str (Buf bfp _ _) bn bc)
  | bn == 0 = return a
  | otherwise = appendWith a bn bc $ \dst -> withForeignPtr bfp $ \src -> copyBytes dst src bn

-- | Append one character given as a code point.
sPush :: Str -> Word32 -> IO Str
sPush s c
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
cmp (Str (Buf fa _ _) na _) (Str (Buf fb _ _) nb _) = unsafeDupablePerformIO $
  withForeignPtr fa $ \pa -> withForeignPtr fb $ \pb -> do
    r <- c_memcmp pa pb (fromIntegral (min na nb))
    return $ case compare r 0 of
      EQ -> compare na nb
      o -> o

sEq, sLt, sLe :: Str -> Str -> Bool
sEq a@(Str _ na _) b@(Str _ nb _) = na == nb && cmp a b == EQ
sLt a b = cmp a b == LT
sLe a b = cmp a b /= GT
