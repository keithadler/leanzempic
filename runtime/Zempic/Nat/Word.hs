-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- FAST PATH: Lean Nat as Word (64-bit). Arithmetic that would exceed 2^64 - 1
-- throws `ZOverflow` instead of wrapping, so a wrong answer cannot happen
-- silently. In auto mode the wrapper catches it and reruns with Zempic.Nat.Exact.
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Zempic.Nat.Word where

import Data.Word (Word16, Word32, Word64, Word8)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Zempic.Arr
import Zempic.Prims (floatOfSci, floatToUnsigned)
import Zempic.Str
import qualified Data.Text as T
import Data.Char (chr, ord)
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Control.Exception (Exception (..), throw)
import GHC.Exts
import Data.List (foldl')
import Zempic.Runtime (Any, zo, zu)
import GHC.Word (Word(W#))

type ZNat = Word

data ZOverflow = ZOverflow

instance Show ZOverflow where
  show _ = "leanzempic: Nat overflow (value exceeds 2^64-1 in word mode)"

instance Exception ZOverflow

overflow :: a
overflow = throw ZOverflow
{-# NOINLINE overflow #-}

natZero :: ZNat
natZero = 0

natAdd, natSub, natMul, natDiv, natMod, natPow, natShr, natShl, natAnd, natOr, natXor, natGcd
  :: ZNat -> ZNat -> ZNat
natAdd (W# a) (W# b) = case addWordC# a b of (# r, 0# #) -> W# r; _ -> overflow
natSub x y = if x >= y then x - y else 0
natMul (W# a) (W# b) = case timesWord2# a b of (# 0##, lo #) -> W# lo; _ -> overflow
natDiv x y = if y == 0 then 0 else quot x y
natMod x y = if y == 0 then x else rem x y
natPow x y
  | y == 0 = 1
  | x <= 1 = x
  | otherwise = go 1 y
  where go !acc 0 = acc
        go !acc n = go (natMul acc x) (n - 1)
natShr x y = if y >= 64 then 0 else shiftR x (fromIntegral y)
natShl x y
  | x == 0 = 0
  | y >= 64 || shiftR (shiftL x (fromIntegral y)) (fromIntegral y) /= x = overflow
  | otherwise = shiftL x (fromIntegral y)
natAnd = (.&.)
natOr = (.|.)
natXor = xor
natGcd = gcd

natEq, natLt, natLe :: ZNat -> ZNat -> Bool
natEq = (==)
natLt = (<)
natLe = (<=)

natSucc :: ZNat -> ZNat
natSucc x = natAdd x 1

{-# INLINE natAdd #-}
{-# INLINE natSub #-}
{-# INLINE natMul #-}
{-# INLINE natDiv #-}
{-# INLINE natMod #-}
{-# INLINE natShr #-}
{-# INLINE natEq #-}
{-# INLINE natLt #-}
{-# INLINE natLe #-}
{-# INLINE natSucc #-}

-- Explicit build so GHC's foldr/build fusion always sees the producer.
zRange :: ZNat -> [Any]
zRange n = map zo (build (\c nil ->
  let go !i = if i >= n then nil else i `c` go (i + 1) in go 0))
{-# INLINE zRange #-}

zLength :: [Any] -> ZNat
zLength xs = fromIntegral (length xs)
{-# INLINE zLength #-}

zSum :: [Any] -> ZNat
zSum = foldl' (\a x -> natAdd a (zu x)) 0
{-# INLINE zSum #-}

zTake :: ZNat -> [Any] -> [Any]
zTake n = take (fromIntegral (min n 4611686018427387903))
{-# INLINE zTake #-}

natOfInteger :: Integer -> ZNat
natOfInteger i = if i > 18446744073709551615 then overflow else fromInteger i

-- (arrGetDW uses runRW# directly: unsafeDupablePerformIO wraps its result in `lazy`, which GHC keeps
-- until CorePrep, so a raw Word read back out of it was boxed again before use.)
-- Array operations on Nat elements without a box (word mode only; see Zempic.Arr.aGetW). The compiler
-- picks these where the element type is Nat and the array is not viewed as another type.
arrGetDW :: Any -> ZNat -> Any -> ZNat -> ZNat
arrGetDW _ (W# d) !a !i = case runRW# (aGetWU (zu a) (arrIdx i) d) of (# _, w #) -> W# w
{-# INLINE arrGetDW #-}

arrSetUW :: Any -> Any -> ZNat -> ZNat -> Any
arrSetUW _ a i v = unsafeDupablePerformIO (zo <$> aSetUW (zu a) (arrIdx i) v)
{-# INLINE arrSetUW #-}

arrPushUW :: Any -> Any -> ZNat -> Any
arrPushUW _ a v = unsafeDupablePerformIO (zo <$> aPushUW (zu a) v)
{-# INLINE arrPushUW #-}

-- BEGIN GENERATED (tools/gen_runtime.py)
-- Conversions between Nat and the fixed-width integers.
u8OfNat :: ZNat -> Word8
u8OfNat = fromIntegral
u8ToNat :: Word8 -> ZNat
u8ToNat = fromIntegral
{-# INLINE u8OfNat #-}
{-# INLINE u8ToNat #-}
u16OfNat :: ZNat -> Word16
u16OfNat = fromIntegral
u16ToNat :: Word16 -> ZNat
u16ToNat = fromIntegral
{-# INLINE u16OfNat #-}
{-# INLINE u16ToNat #-}
u32OfNat :: ZNat -> Word32
u32OfNat = fromIntegral
u32ToNat :: Word32 -> ZNat
u32ToNat = fromIntegral
{-# INLINE u32OfNat #-}
{-# INLINE u32ToNat #-}
u64OfNat :: ZNat -> Word64
u64OfNat = fromIntegral
u64ToNat :: Word64 -> ZNat
u64ToNat = fromIntegral
{-# INLINE u64OfNat #-}
{-# INLINE u64ToNat #-}
uszOfNat :: ZNat -> Word
uszOfNat = fromIntegral
uszToNat :: Word -> ZNat
uszToNat = fromIntegral
{-# INLINE uszOfNat #-}
{-# INLINE uszToNat #-}
u8OfNatLT :: ZNat -> Any -> Word8
u8OfNatLT n _ = fromIntegral n
{-# INLINE u8OfNatLT #-}
u16OfNatLT :: ZNat -> Any -> Word16
u16OfNatLT n _ = fromIntegral n
{-# INLINE u16OfNatLT #-}
u32OfNatLT :: ZNat -> Any -> Word32
u32OfNatLT n _ = fromIntegral n
{-# INLINE u32OfNatLT #-}
u64OfNatLT :: ZNat -> Any -> Word64
u64OfNatLT n _ = fromIntegral n
{-# INLINE u64OfNatLT #-}
uszOfNatLT :: ZNat -> Any -> Word
uszOfNatLT n _ = fromIntegral n
{-# INLINE uszOfNatLT #-}
-- Lean's Array as a Baker persistent array (see Zempic.Arr): O(1) at the newest version.
arrIdx :: ZNat -> Int
arrIdx i = fromIntegral (min i 4611686018427387903)
{-# INLINE arrIdx #-}

arrIO :: IO a -> a
arrIO = unsafeDupablePerformIO
{-# INLINE arrIO #-}

-- A handle that copies the array on its first write (see Zempic.Arr.aShare).
arrShare :: Any -> Any
arrShare a = arrIO (zo <$> aShare (zu a))
{-# NOINLINE arrShare #-}

arrMkEmpty :: Any -> ZNat -> Any
arrMkEmpty _ c = arrIO (zo <$> aEmpty (arrIdx c))
{-# NOINLINE arrMkEmpty #-}

-- Creation with an unboxed element representation, chosen by the compiler from the element type
-- (kind codes in Zempic.Arr): 1 Word8, 2 Word16, 3 Word32, 4 Word64, 5 Word, 6 Bool.
arrMkEmptyK :: Int -> Any -> ZNat -> Any
arrMkEmptyK k _ c = arrIO (zo <$> aEmptyK k (arrIdx c))
{-# NOINLINE arrMkEmptyK #-}

arrReplicateK :: Int -> Any -> ZNat -> Any -> Any
arrReplicateK k _ n v = arrIO (zo <$> aReplicateK k (arrIdx n) v)
{-# NOINLINE arrReplicateK #-}

arrOfListK :: Int -> Any -> [Any] -> Any
arrOfListK k _ xs = arrIO (zo <$> aFromListK k xs)
{-# NOINLINE arrOfListK #-}

-- Writes through a view of the array as boxed values of another type (Lean's in-place Array.map treats
-- an `Array Nat` as `Array NonScalar` and stores the results, whatever their type): make the buffer
-- boxed first, so a value of the wrong type never lands in an unboxed buffer.
arrSetB :: Any -> Any -> ZNat -> Any -> Any
arrSetB _ !a !i !v = arrIO (aDeopt (zu a) >> (zo <$> aSet (zu a) (arrIdx i) v))
{-# NOINLINE arrSetB #-}

arrSetBU :: Any -> Any -> ZNat -> Any -> Any
arrSetBU _ a i v = arrIO (aDeopt (zu a) >> (zo <$> aSetU (zu a) (arrIdx i) v))
{-# NOINLINE arrSetBU #-}

arrSetHB :: Any -> Any -> ZNat -> Any -> Any -> Any
arrSetHB _ !a !i !v _ = arrIO (aDeopt (zu a) >> (zo <$> aSet (zu a) (arrIdx i) v))
{-# NOINLINE arrSetHB #-}

arrSetHBU :: Any -> Any -> ZNat -> Any -> Any -> Any
arrSetHBU _ a i v _ = arrIO (aDeopt (zu a) >> (zo <$> aSetU (zu a) (arrIdx i) v))
{-# NOINLINE arrSetHBU #-}

arrUSetB :: Any -> Any -> Word -> Any -> Any -> Any
arrUSetB _ a i v _ = arrIO (aDeopt (zu a) >> (zo <$> aSet (zu a) (fromIntegral i) v))
{-# NOINLINE arrUSetB #-}

arrUSetBU :: Any -> Any -> Word -> Any -> Any -> Any
arrUSetBU _ a i v _ = arrIO (aDeopt (zu a) >> (zo <$> aSetU (zu a) (fromIntegral i) v))
{-# NOINLINE arrUSetBU #-}

arrPushB :: Any -> Any -> Any -> Any
arrPushB _ !a !v = arrIO (aDeopt (zu a) >> (zo <$> aPush (zu a) v))
{-# NOINLINE arrPushB #-}

arrPushBU :: Any -> Any -> Any -> Any
arrPushBU _ a v = arrIO (aDeopt (zu a) >> (zo <$> aPushU (zu a) v))
{-# NOINLINE arrPushBU #-}

arrReplicate :: Any -> ZNat -> Any -> Any
arrReplicate _ n v = arrIO (zo <$> aReplicate (arrIdx n) v)
{-# NOINLINE arrReplicate #-}

arrSize :: Any -> Any -> ZNat
arrSize _ a = fromIntegral (aLength (zu a :: Arr))

arrUSize :: Any -> Any -> Word
arrUSize _ a = fromIntegral (aLength (zu a :: Arr))

arrPush :: Any -> Any -> Any -> Any
arrPush _ !a !v = arrIO (zo <$> aPush (zu a) v)
{-# INLINE arrPush #-}

arrGetD :: Any -> Any -> Any -> ZNat -> Any
arrGetD _ !d !a !i = arrIO (aGet (zu a) (arrIdx i) d)
{-# INLINE arrGetD #-}

arrGetI :: Any -> Any -> ZNat -> Any -> Any
arrGetI _ a i _ = arrIO (aGet (zu a) (arrIdx i) (error "leanzempic: array index out of range"))
{-# NOINLINE arrGetI #-}

arrUGet :: Any -> Any -> Word -> Any -> Any
arrUGet _ a i _ = arrIO (aGet (zu a) (fromIntegral i) (error "leanzempic: array index out of range"))
{-# NOINLINE arrUGet #-}

arrSet :: Any -> Any -> ZNat -> Any -> Any
arrSet _ !a !i !v = arrIO (zo <$> aSet (zu a) (arrIdx i) v)
{-# INLINE arrSet #-}

arrSetH :: Any -> Any -> ZNat -> Any -> Any -> Any
arrSetH _ !a !i !v _ = arrIO (zo <$> aSet (zu a) (arrIdx i) v)
{-# INLINE arrSetH #-}

arrUSet :: Any -> Any -> Word -> Any -> Any -> Any
arrUSet _ a i v _ = arrIO (zo <$> aSet (zu a) (fromIntegral i) v)
{-# INLINE arrUSet #-}

arrSwap :: Any -> Any -> ZNat -> ZNat -> Any
arrSwap _ a i j = arrIO (zo <$> aSwap (zu a) (arrIdx i) (arrIdx j))
{-# NOINLINE arrSwap #-}

arrPop :: Any -> Any -> Any
arrPop _ a = arrIO (zo <$> aPop (zu a))
{-# NOINLINE arrPop #-}

arrSwapP :: Any -> Any -> ZNat -> ZNat -> Any -> Any -> Any
arrSwapP _ a i j _ _ = arrIO (zo <$> aSwap (zu a) (arrIdx i) (arrIdx j))
{-# NOINLINE arrSwapP #-}

-- In-place variants, used only where the compiler proved the array unshared (see Zempic.Own).
arrSetU :: Any -> Any -> ZNat -> Any -> Any
arrSetU _ a i v = arrIO (zo <$> aSetU (zu a) (arrIdx i) v)
{-# NOINLINE arrSetU #-}

arrUSetU :: Any -> Any -> Word -> Any -> Any -> Any
arrUSetU _ a i v _ = arrIO (zo <$> aSetU (zu a) (fromIntegral i) v)
{-# NOINLINE arrUSetU #-}

arrPushU :: Any -> Any -> Any -> Any
arrPushU _ a v = arrIO (zo <$> aPushU (zu a) v)
{-# NOINLINE arrPushU #-}

arrPopU :: Any -> Any -> Any
arrPopU _ a = arrIO (zo <$> aPopU (zu a))
{-# NOINLINE arrPopU #-}

arrSwapU :: Any -> Any -> ZNat -> ZNat -> Any
arrSwapU _ a i j = arrIO (zo <$> aSwapU (zu a) (arrIdx i) (arrIdx j))
{-# NOINLINE arrSwapU #-}

arrSwapPU :: Any -> Any -> ZNat -> ZNat -> Any -> Any -> Any
arrSwapPU _ a i j _ _ = arrIO (zo <$> aSwapU (zu a) (arrIdx i) (arrIdx j))
{-# NOINLINE arrSwapPU #-}

arrOfList :: Any -> [Any] -> Any
arrOfList _ xs = arrIO (zo <$> aFromList xs)
{-# NOINLINE arrOfList #-}

arrToList :: Any -> Any -> [Any]
arrToList _ a = arrIO (aToList (zu a))
{-# NOINLINE arrToList #-}

-- Lean's String as a shared UTF-8 buffer (see Zempic.Str): amortized O(1) push and append.
strIO :: IO a -> a
strIO = unsafeDupablePerformIO
{-# INLINE strIO #-}

strLen :: Any -> ZNat
strLen s = fromIntegral (sChars (zu s :: Str))

strBytes :: Any -> ZNat
strBytes s = fromIntegral (sBytes (zu s :: Str))

strAppend :: Any -> Any -> Any
strAppend a b = strIO (zo <$> sAppend (zu a) (zu b))
{-# NOINLINE strAppend #-}

strPush :: Any -> Word32 -> Any
strPush s c = strIO (zo <$> sPush (zu s) c)
{-# NOINLINE strPush #-}

strEq, strLt, strLe :: Any -> Any -> Bool
strEq a b = sEq (zu a :: Str) (zu b :: Str)
strLt a b = sLt (zu a :: Str) (zu b :: Str)
strLe a b = sLe (zu a :: Str) (zu b :: Str)

strToList :: Any -> [Any]
strToList s = map (\c -> zo (fromIntegral (ord c) :: Word32)) (T.unpack (sToText (zu s :: Str)))

strOfList :: [Any] -> Any
strOfList cs = strIO (zo <$> sFromText (T.pack (map (\c -> chr (fromIntegral (zu c :: Word32))) cs)))
{-# NOINLINE strOfList #-}

natRepr :: ZNat -> Any
natRepr n = strIO (zo <$> sFromIntegral n)
{-# NOINLINE natRepr #-}

-- Lean's panic prints a message to stderr and carries on with the default value. This carries on
-- with the default silently (the message is not reproduced).
panicCore :: Any -> Any -> Any -> Any
panicCore _ d _ = d

strLit :: String -> Any
strLit lit = strIO (zo <$> sFromText (T.pack lit))
{-# NOINLINE strLit #-}

-- Strings by byte position (a Pos is a byte offset).
strGet :: Any -> ZNat -> Word32
strGet s p = sCharAt (zu s :: Str) (arrIdx p)
{-# INLINE strGet #-}

strNext :: Any -> ZNat -> ZNat
strNext s p = natAdd p (fromIntegral (sCharWidthAt (zu s :: Str) (arrIdx p)))
{-# INLINE strNext #-}

strPrev :: Any -> ZNat -> ZNat
strPrev s p = fromIntegral (sPrev (zu s :: Str) (arrIdx p))
{-# INLINE strPrev #-}

strAtEnd :: Any -> ZNat -> Bool
strAtEnd s p = toInteger p >= toInteger (sBytes (zu s :: Str))
{-# INLINE strAtEnd #-}

strExtract :: Any -> ZNat -> ZNat -> Any
strExtract s b e = strIO (zo <$> sExtract (zu s) (arrIdx b) (arrIdx e))
{-# NOINLINE strExtract #-}

strPushn :: Any -> Word32 -> ZNat -> Any
strPushn s c n = strIO (zo <$> sPushn (zu s) c (arrIdx n))
{-# NOINLINE strPushn #-}

strDecodeChar :: Any -> ZNat -> Any -> Word32
strDecodeChar s p _ = strGet s p
{-# INLINE strDecodeChar #-}

strPosNext :: Any -> ZNat -> Any -> ZNat
strPosNext s p _ = strNext s p
{-# INLINE strPosNext #-}

strGetByte :: Any -> ZNat -> Any -> Word8
strGetByte s i _ = sByteAt (zu s :: Str) (arrIdx i)
{-# INLINE strGetByte #-}

strPosOf :: Any -> Word32 -> ZNat
strPosOf s c = go 0
  where st = zu s :: Str
        n = sBytes st
        go i | i >= n = fromIntegral n
             | sCharAt st i == c = fromIntegral i
             | otherwise = go (i + sCharWidthAt st i)

strOffsetOfPos :: Any -> ZNat -> ZNat
strOffsetOfPos s p = go 0 0
  where st = zu s :: Str
        lim = min (arrIdx p) (sBytes st)
        go i acc | i >= lim = acc
                 | otherwise = go (i + sCharWidthAt st i) (acc + 1)

strHash :: Any -> Word64
strHash s = sHash (zu s :: Str)

strMemcmp :: Any -> Any -> ZNat -> ZNat -> ZNat -> Any -> Any -> Bool
strMemcmp a b i j len _ _ = sMemEq (zu a :: Str) (zu b :: Str) (arrIdx i) (arrIdx j) (arrIdx len)

strSetAt :: Any -> ZNat -> Word32 -> Any
strSetAt s p c =
  let st = zu s :: Str
      i = arrIdx p
  in if i >= sBytes st || p < 0 then s
     else strIO (do pre <- sExtract st 0 i
                    mid <- sPush pre c
                    rest <- sExtract st (i + sCharWidthAt st i) (sBytes st)
                    zo <$> sAppend mid rest)
{-# NOINLINE strSetAt #-}

strSetAtH :: Any -> ZNat -> Word32 -> Any -> Any
strSetAtH s p c _ = strSetAt s p c

natLog2 :: ZNat -> ZNat
natLog2 n = if n == 0 then 0 else go 0 (toInteger n)
  where go acc x = if x <= 1 then acc else go (acc + 1) (x `shiftR` 1)

natPred :: ZNat -> ZNat
natPred x = if x == 0 then 0 else x - 1

strIsEmpty :: Any -> Bool
strIsEmpty s = sBytes (zu s :: Str) == 0
{-# INLINE strIsEmpty #-}

-- Int (an Integer), converting to and from Nat.
intOfNat :: ZNat -> Integer
intOfNat = toInteger
{-# INLINE intOfNat #-}

intNegSucc :: ZNat -> Integer
intNegSucc n = negate (toInteger n) - 1

intToNat :: Integer -> ZNat
intToNat i = if i < 0 then 0 else natOfInteger i

intNatAbs :: Integer -> ZNat
intNatAbs i = natOfInteger (abs i)

intPow :: Integer -> ZNat -> Integer
intPow b e = b ^ toInteger e

floatOfNat :: ZNat -> Double
floatOfNat = fromIntegral

floatOfInt :: Integer -> Double
floatOfInt = fromInteger

floatOfSciN :: ZNat -> Bool -> ZNat -> Double
floatOfSciN m neg e = floatOfSci (toInteger m) neg (toInteger e)

floatToU8 :: Double -> Word8
floatToU8 x = fromInteger (floatToUnsigned 255 x)
floatToU16 :: Double -> Word16
floatToU16 x = fromInteger (floatToUnsigned 65535 x)
floatToU32 :: Double -> Word32
floatToU32 x = fromInteger (floatToUnsigned 4294967295 x)
floatToU64 :: Double -> Word64
floatToU64 x = fromInteger (floatToUnsigned 18446744073709551615 x)
floatToUsz :: Double -> Word
floatToUsz x = fromInteger (floatToUnsigned 18446744073709551615 x)

-- ByteArray, kept in the same shared buffer as strings (bytes only).
baEmpty :: ZNat -> Any
baEmpty _ = strIO (zo <$> sFromText T.empty)
{-# NOINLINE baEmpty #-}

baSize :: Any -> ZNat
baSize a = fromIntegral (sBytes (zu a :: Str))

baPush :: Any -> Word8 -> Any
baPush a b = strIO (zo <$> sPushByte (zu a) b)
{-# NOINLINE baPush #-}

baGet :: Any -> ZNat -> Word8
baGet a i = let s = zu a :: Str; k = arrIdx i in if k < sBytes s then sByteAt s k else 0

baGetF :: Any -> ZNat -> Any -> Word8
baGetF a i _ = baGet a i

baUGet :: Any -> Word -> Any -> Word8
baUGet a i _ = baGet a (fromIntegral i)

baSet :: Any -> ZNat -> Word8 -> Any
baSet a i b = strIO (zo <$> sSetByte (zu a) (arrIdx i) b)
{-# NOINLINE baSet #-}

charOfNat :: ZNat -> Word32
charOfNat n = if n < 55296 || (n > 57343 && n < 1114112) then fromIntegral n else 0
charOfNatAux :: ZNat -> Any -> Word32
charOfNatAux n _ = fromIntegral n
{-# INLINE charOfNat #-}
{-# INLINE charOfNatAux #-}
-- END GENERATED
