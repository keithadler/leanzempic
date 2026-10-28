{-# LANGUAGE BangPatterns #-}
-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Exact Lean Nat as Haskell Natural (arbitrary precision).
module Zempic.Nat.Exact where

import Data.Word (Word16, Word32, Word64, Word8)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Zempic.Arr
import Zempic.Str
import qualified Data.Text as T
import Data.Char (chr, ord)
import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import GHC.Exts (build)
import Numeric.Natural (Natural)
import Data.List (foldl')
import Zempic.Runtime (Any, zo, zu)

type ZNat = Natural

natZero :: ZNat
natZero = 0

natAdd, natSub, natMul, natDiv, natMod, natPow, natShr, natShl, natAnd, natOr, natXor, natGcd
  :: ZNat -> ZNat -> ZNat
natAdd = (+)
natSub x y = if x >= y then x - y else 0
natMul = (*)
natDiv x y = if y == 0 then 0 else quot x y
natMod x y = if y == 0 then x else rem x y
natPow = (^)
natShr x y = shiftR x (fromIntegral y)
natShl x y = shiftL x (fromIntegral y)
natAnd = (.&.)
natOr = (.|.)
natXor = xor
natGcd = gcd

natEq, natLt, natLe :: ZNat -> ZNat -> Bool
natEq = (==)
natLt = (<)
natLe = (<=)

natSucc :: ZNat -> ZNat
natSucc = (+ 1)

{-# INLINE natAdd #-}
{-# INLINE natSub #-}
{-# INLINE natMul #-}
{-# INLINE natDiv #-}
{-# INLINE natMod #-}
{-# INLINE natPow #-}
{-# INLINE natShr #-}
{-# INLINE natShl #-}
{-# INLINE natAnd #-}
{-# INLINE natOr #-}
{-# INLINE natXor #-}
{-# INLINE natGcd #-}
{-# INLINE natEq #-}
{-# INLINE natLt #-}
{-# INLINE natLe #-}
{-# INLINE natSucc #-}

-- Explicit build so GHC's foldr/build fusion always sees the producer.
zRange :: ZNat -> [Any]
zRange n = map zo (build (\c nil ->
  let go i = if i >= n then nil else i `c` go (i + 1) in go 0))
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
-- Lean's Array as a Baker persistent array (see Zempic.Arr): O(1) at the newest version.
arrIdx :: ZNat -> Int
arrIdx i = fromIntegral (min i 4611686018427387903)
{-# INLINE arrIdx #-}

arrIO :: IO a -> a
arrIO = unsafeDupablePerformIO
{-# INLINE arrIO #-}

arrMkEmpty :: Any -> ZNat -> Any
arrMkEmpty _ c = arrIO (zo <$> aEmpty (arrIdx c))
{-# NOINLINE arrMkEmpty #-}

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
natRepr n = strIO (zo <$> sFromText (T.pack (show n)))
{-# NOINLINE natRepr #-}

strLit :: String -> Any
strLit lit = strIO (zo <$> sFromText (T.pack lit))
{-# NOINLINE strLit #-}

charOfNat :: ZNat -> Word32
charOfNat n = if n < 55296 || (n > 57343 && n < 1114112) then fromIntegral n else 0
charOfNatAux :: ZNat -> Any -> Word32
charOfNatAux n _ = fromIntegral n
{-# INLINE charOfNat #-}
{-# INLINE charOfNatAux #-}
-- END GENERATED
