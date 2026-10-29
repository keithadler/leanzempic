{-# LANGUAGE BangPatterns #-}
-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- Model-based randomized tests of the Haskell runtime. Each structure is driven through long random
-- sequences of operations and compared, after every step, with a plain pure model. Old versions are
-- read again after newer ones were made, which is exactly what persistence has to get right.
--
-- Run:  ghc -O1 -iruntime tests/PropTests.hs -o build/proptests && build/proptests [seed] [rounds]
module Main (main) where

import Control.Monad (foldM, forM_, replicateM, unless, when)
import qualified Data.ByteString as B
import Data.Bits (complement, shiftL, shiftR, xor, (.&.), (.|.))
import Data.IORef
import Data.List (foldl')
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word
import GHC.Exts (Any)
import Numeric.Natural (Natural)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Unsafe.Coerce (unsafeCoerce)

import Control.Exception (SomeException, evaluate, try)
import qualified Zempic.Arr as A
import qualified Zempic.Nat.Exact as E
import qualified Zempic.Nat.Word as W
import qualified Zempic.Str as S
import qualified Zempic.UInt as U

-- * A small deterministic generator (xorshift64*), so a failure can be replayed by seed

newtype Gen = Gen (IORef Word64)

next :: Gen -> IO Word64
next (Gen r) = do
  x0 <- readIORef r
  let x1 = x0 `xor` (x0 `shiftR` 12)
      x2 = x1 `xor` (x1 `shiftL` 25)
      x3 = x2 `xor` (x2 `shiftR` 27)
  writeIORef r x3
  return (x3 * 0x2545F4914F6CDD1D)

below :: Gen -> Int -> IO Int
below g n = (\w -> fromIntegral (w `shiftR` 11) `mod` max 1 n) <$> next g

-- | Random element of a list.
pick :: Gen -> [a] -> IO a
pick g xs = (xs !!) <$> below g (length xs)

-- * Failure reporting

type Check = IORef [String]

failWith :: Check -> String -> IO ()
failWith c msg = modifyIORef c (msg :)

expect :: (Eq a, Show a) => Check -> String -> a -> a -> IO ()
expect c what got want = unless (got == want) $ failWith c (what ++ ": got " ++ show got ++ ", want " ++ show want)

-- * Arrays against a list model

-- | The element kinds of an array (see Zempic.Arr): 0 boxed Int, 1 Word8, 2 Word16, 3 Word32,
-- 4 Word64, 5 Word, 6 Bool. A test value is an Int small enough for every kind.
lim :: Int -> Int
lim 1 = 256
lim 6 = 2
lim _ = 1000

enc :: Int -> Int -> Any
enc 1 v = unsafeCoerce (fromIntegral v :: Word8)
enc 2 v = unsafeCoerce (fromIntegral v :: Word16)
enc 3 v = unsafeCoerce (fromIntegral v :: Word32)
enc 4 v = unsafeCoerce (fromIntegral v :: Word64)
enc 5 v = unsafeCoerce (fromIntegral v :: Word)
enc 6 v = unsafeCoerce (v /= 0)
enc _ v = unsafeCoerce v

dec :: Int -> Any -> Int
dec 1 a = fromIntegral (unsafeCoerce a :: Word8)
dec 2 a = fromIntegral (unsafeCoerce a :: Word16)
dec 3 a = fromIntegral (unsafeCoerce a :: Word32)
dec 4 a = fromIntegral (unsafeCoerce a :: Word64)
dec 5 a = fromIntegral (unsafeCoerce a :: Word)
dec 6 a = if (unsafeCoerce a :: Bool) then 1 else 0
dec _ a = unsafeCoerce a

-- | What a value becomes after one round trip through the kind's representation.
norm :: Int -> Int -> Int
norm k v = dec k (enc k v)

-- | Lean's library stores this in a slot to drop a reference before writing the element back.
placeholder :: Any
placeholder = unsafeCoerce ()

modelSet :: Int -> Int -> [Int] -> [Int]
modelSet k v m
  | k < 0 || k >= length m = m
  | otherwise = take k m ++ [v] ++ drop (k + 1) m

modelSwap :: Int -> Int -> [Int] -> [Int]
modelSwap i j m
  | i < 0 || j < 0 || i >= n || j >= n = m
  | otherwise = modelSet j (m !! i) (modelSet i (m !! j) m)
  where n = length m

arrContents :: Int -> A.Arr -> IO [Int]
arrContents kind a = map (dec kind) <$> A.aToList a

-- | Persistent operations on a pool of versions; any version may be read or extended at any time.
arrPersistent :: Check -> Gen -> Int -> Int -> IO ()
arrPersistent c g kind steps = do
  a0 <- A.aEmptyK kind 4
  pool <- newIORef [(a0, [] :: [Int])]
  forM_ [1 .. steps] $ \step -> do
    vs <- readIORef pool
    i <- below g (length vs)
    let (a, m) = vs !! i
    -- Re-read the chosen (possibly old) version in full first.
    got <- arrContents kind a
    expect c ("step " ++ show step ++ " old version contents") got m
    expect c "length" (A.aLength a) (length m)
    op <- below g 8
    k <- subtract 1 <$> below g (length m + 3)
    v <- below g (lim kind)
    new <- case op of
      0 -> do b <- A.aPush a (enc kind v); return (Just (b, m ++ [v]))
      1 -> do b <- A.aPop a; return (Just (b, if null m then m else init m))
      2 -> do b <- A.aSet a k (enc kind v); return (Just (b, modelSet k v m))
      3 -> do
        j <- subtract 1 <$> below g (length m + 3)
        b <- A.aSwap a k j
        return (Just (b, modelSwap k j m))
      4 -> do
        r <- A.aGet a k (enc kind (-7))
        expect c "get" (dec kind r) (if k >= 0 && k < length m then m !! k else norm kind (-7))
        return Nothing
      6 -> do
        -- Making the buffer boxed must not change what any version reads.
        A.aDeopt a
        got2 <- arrContents kind a
        expect c "contents unchanged by aDeopt" got2 m
        return Nothing
      7 -> do
        -- As Array.modify and swapAt do: store the placeholder to drop the reference, then write the real
        -- value to the same slot. An unboxed buffer ignores the placeholder, a boxed one stores it; the
        -- result and every older version must read correctly either way.
        b1 <- A.aSet a k placeholder
        b2 <- A.aSet b1 k (enc kind v)
        return (Just (b2, modelSet k v m))
      _ -> do
        n <- below g 3
        b <- foldM (\x j -> A.aPush x (enc kind ((v + j) `mod` lim kind))) a [1 .. n]
        return (Just (b, m ++ [(v + j) `mod` lim kind | j <- [1 .. n]]))
    case new of
      Nothing -> return ()
      Just (b, mb) -> do
        gb <- arrContents kind b
        expect c "new version contents" gb mb
        modifyIORef pool (\p -> if length p < 40 then (b, mb) : p else (b, mb) : take 39 p)
  -- Every surviving version must still read correctly after all the later ones were made.
  final <- readIORef pool
  forM_ (zip [0 :: Int ..] final) $ \(i, (a, m)) -> do
    got <- arrContents kind a
    expect c ("final pool member " ++ show i) got m

-- | A placeholder written to a fresh unboxed buffer must change nothing: it is not an element of the
-- buffer's type, so the buffer ignores it. (Lean's library writes one before writing the real value back;
-- storing it would read a unit closure as a number.)
arrPlaceholderRaw :: Check -> Gen -> Int -> IO ()
arrPlaceholderRaw c g kind = do
  a0 <- A.aEmptyK kind 4
  n <- (+ 3) <$> below g 20
  vals <- replicateM n (below g (lim kind))
  a <- foldM (\x v -> A.aPush x (enc kind v)) a0 vals
  forM_ [0 .. n - 1] $ \i -> do
    b <- A.aSet a i placeholder
    got <- arrContents kind b
    expect c ("kind " ++ show kind ++ " placeholder at " ++ show i ++ " leaves the buffer unchanged") got vals

-- | The in-place variants on a single owner, then on a stale version (they must fall back).
arrInPlace :: Check -> Gen -> Int -> Int -> IO ()
arrInPlace c g kind steps = do
  a0 <- A.aEmptyK kind 2
  (aEnd, mEnd) <- foldM
    (\(a, m) _ -> do
        op <- below g 4
        k <- subtract 1 <$> below g (length m + 3)
        v <- below g (lim kind)
        (b, mb) <- case op of
          0 -> do b <- A.aPushU a (enc kind v); return (b, m ++ [v])
          1 -> do b <- A.aPopU a; return (b, if null m then m else init m)
          2 -> do b <- A.aSetU a k (enc kind v); return (b, modelSet k v m)
          _ -> do
            j <- subtract 1 <$> below g (length m + 3)
            b <- A.aSwapU a k j
            return (b, modelSwap k j m)
        got <- arrContents kind b
        expect c "in-place result" got mb
        return (b, mb))
    (a0, []) [1 .. steps]
  -- Make the end version stale by extending it persistently, then misuse it with in-place ops.
  newer <- A.aPush aEnd (enc kind 4242)
  stale1 <- A.aPushU aEnd (enc kind 7)
  gs <- arrContents kind stale1
  expect c "stale in-place push falls back" gs (mEnd ++ [norm kind 7])
  stale2 <- A.aSetU aEnd 0 (enc kind 9)
  g2 <- arrContents kind stale2
  expect c "stale in-place set falls back" g2 (modelSet 0 (norm kind 9) mEnd)
  gn <- arrContents kind newer
  expect c "the newer version is undisturbed by stale in-place ops" gn (mEnd ++ [norm kind 4242])
  g0 <- arrContents kind aEnd
  expect c "the stale version itself is undisturbed" g0 mEnd

-- * Strings against a Text model

codepoint :: Gen -> IO Word32
codepoint g = do
  r <- below g 5
  case r of
    0 -> fromIntegral <$> below g 0x80
    1 -> fromIntegral . (+ 0x80) <$> below g (0x800 - 0x80)
    2 -> fromIntegral . (+ 0x800) <$> below g (0xD800 - 0x800)
    3 -> fromIntegral . (+ 0xE000) <$> below g (0x10000 - 0xE000)
    _ -> fromIntegral . (+ 0x10000) <$> below g (0x110000 - 0x10000)

strCheck :: Check -> String -> S.Str -> String -> IO ()
strCheck c what s m = do
  expect c (what ++ " contents") (T.unpack (S.sToText s)) m
  expect c (what ++ " chars") (S.sChars s) (length m)
  expect c (what ++ " bytes") (S.sBytes s) (B.length (TE.encodeUtf8 (T.pack m)))

strPool :: Check -> Gen -> Int -> IO ()
strPool c g steps = do
  s0 <- S.sFromText T.empty
  pool <- newIORef [(s0, "")]
  forM_ [1 .. steps] $ \step -> do
    vs <- readIORef pool
    i <- below g (length vs)
    j <- below g (length vs)
    let (s, m) = vs !! i
        (t, mt) = vs !! j
    strCheck c ("step " ++ show step ++ " old version") s m
    op <- below g 6
    new <- case op of
      0 -> do
        cp <- codepoint g
        r <- S.sPush s cp
        return (Just (r, m ++ [toEnum (fromIntegral cp)]))
      1 -> do r <- S.sAppend s t; return (Just (r, m ++ mt))
      2 -> do r <- S.sAppend s s; return (Just (r, m ++ m))
      3 -> do
        expect c "eq" (S.sEq s t) (m == mt)
        expect c "lt" (S.sLt s t) (m < mt)
        expect c "le" (S.sLe s t) (m <= mt)
        return Nothing
      4 -> do
        n <- below g 20
        r <- foldM (\x _ -> codepoint g >>= S.sPush x) s [1 .. n]
        -- pushes are random, so recompute the model from the result's text
        return (Just (r, T.unpack (S.sToText r)))
      _ -> do
        n <- below g 100000
        r <- S.sFromIntegral (fromIntegral n :: Word)
        return (Just (r, show n))
    case new of
      Nothing -> return ()
      Just (r, mr) -> do
        strCheck c "new version" r mr
        modifyIORef pool (\p -> if length p < 30 then (r, mr) : p else (r, mr) : take 29 p)
  final <- readIORef pool
  forM_ (zip [0 :: Int ..] final) $ \(i, (s, m)) -> strCheck c ("final pool member " ++ show i) s m

-- * Fixed-width integers against Integer arithmetic

edge :: Integer -> [Integer]
edge m = [0, 1, 2, 3, m - 1, m - 2, m `div` 2, m `div` 2 + 1]

uintType :: (Show a, Integral a, Bounded a) => Check -> Gen -> String -> Int
         -> [(String, a -> a -> a, Integer -> Integer -> Integer)] -> IO ()
uintType c g name bits ops = do
  let m = 2 ^ bits :: Integer
  forM_ [1 .. 3000 :: Int] $ \_ -> do
    a <- operand m
    b <- operand m
    forM_ ops $ \(opName, f, ref) ->
      expect c (name ++ "." ++ opName ++ " " ++ show a ++ " " ++ show b)
        (toInteger (f (fromInteger a) (fromInteger b))) (ref a b `mod` m)
  where
    operand m = do
      useEdge <- below g 4
      if useEdge == 0 then pick g (edge m) else (`mod` m) . toInteger <$> next g

-- | Lean's semantics: wrapping; division by zero is 0; modulo by zero is the dividend; shifts are
-- taken modulo the bit width.
uintOps :: Int -> [(String, Integer -> Integer -> Integer)]
uintOps bits =
  [ ("add", (+)), ("sub", (-)), ("mul", (*))
  , ("div", \a b -> if b == 0 then 0 else a `div` b)
  , ("mod", \a b -> if b == 0 then a else a `mod` b)
  , ("land", (.&.)), ("lor", (.|.)), ("xor", xor)
  , ("shl", \a b -> a * 2 ^ (b `mod` toInteger bits))
  , ("shr", \a b -> a `div` 2 ^ (b `mod` toInteger bits)) ]
  where _ = bits

-- * Nat: the word fast path against the exact one

natCompare :: Check -> Gen -> IO ()
natCompare c g = do
  let two64 = 2 ^ (64 :: Int) :: Integer
      ops :: [(String, Word -> Word -> Word, Natural -> Natural -> Natural, Integer -> Integer -> Integer)]
      ops = [ ("add", W.natAdd, E.natAdd, (+)), ("mul", W.natMul, E.natMul, (*))
            , ("sub", W.natSub, E.natSub, \a b -> max 0 (a - b))
            , ("div", W.natDiv, E.natDiv, \a b -> if b == 0 then 0 else a `div` b)
            , ("mod", W.natMod, E.natMod, \a b -> if b == 0 then a else a `mod` b)
            , ("and", W.natAnd, E.natAnd, (.&.)), ("or", W.natOr, E.natOr, (.|.)), ("xor", W.natXor, E.natXor, xor) ]
  forM_ [1 .. 4000 :: Int] $ \_ -> do
    useEdge <- below g 3
    a <- if useEdge == 0 then pick g (edge two64) else (`mod` two64) . toInteger <$> next g
    b <- if useEdge == 0 then pick g (edge two64) else (`mod` two64) . toInteger <$> next g
    forM_ ops $ \(name, wf, ef, ref) -> do
      let truth = ref a b
          exact = toInteger (ef (fromInteger a) (fromInteger b))
      expect c ("exact." ++ name) exact truth
      r <- try (evaluate (wf (fromInteger a) (fromInteger b)))
      case r of
        Right w -> expect c ("word." ++ name ++ " " ++ show a ++ " " ++ show b) (toInteger w) truth
        Left e -> when (truth < two64) $
          failWith c ("word." ++ name ++ " threw although the true result " ++ show truth
                      ++ " fits: " ++ show (e :: SomeException))

-- * Driver

main :: IO ()
main = do
  args <- getArgs
  let seed = case args of (s : _) -> read s; _ -> 12345 :: Word64
      rounds = case args of (_ : r : _) -> read r; _ -> 6 :: Int
  gen <- Gen <$> newIORef (seed * 0x9E3779B97F4A7C15 + 1)
  check <- newIORef []
  putStrLn ("proptests: seed " ++ show seed ++ ", " ++ show rounds ++ " rounds")
  forM_ [1 .. rounds] $ \_ -> do
    forM_ [0 .. 6] $ \kind -> do
      arrPersistent check gen kind 600
      arrInPlace check gen kind 400
      when (kind /= 0) $ arrPlaceholderRaw check gen kind
    strPool check gen 500
  uintType check gen "UInt8" 8 [ (n, f, r) | ((n, r), f) <- zip (uintOps 8)
    [U.u8Add, U.u8Sub, U.u8Mul, U.u8Div, U.u8Mod, U.u8Land, U.u8Lor, U.u8Xor, U.u8Shl, U.u8Shr] ]
  uintType check gen "UInt16" 16 [ (n, f, r) | ((n, r), f) <- zip (uintOps 16)
    [U.u16Add, U.u16Sub, U.u16Mul, U.u16Div, U.u16Mod, U.u16Land, U.u16Lor, U.u16Xor, U.u16Shl, U.u16Shr] ]
  uintType check gen "UInt32" 32 [ (n, f, r) | ((n, r), f) <- zip (uintOps 32)
    [U.u32Add, U.u32Sub, U.u32Mul, U.u32Div, U.u32Mod, U.u32Land, U.u32Lor, U.u32Xor, U.u32Shl, U.u32Shr] ]
  uintType check gen "UInt64" 64 [ (n, f, r) | ((n, r), f) <- zip (uintOps 64)
    [U.u64Add, U.u64Sub, U.u64Mul, U.u64Div, U.u64Mod, U.u64Land, U.u64Lor, U.u64Xor, U.u64Shl, U.u64Shr] ]
  uintType check gen "USize" 64 [ (n, f, r) | ((n, r), f) <- zip (uintOps 64)
    [U.uszAdd, U.uszSub, U.uszMul, U.uszDiv, U.uszMod, U.uszLand, U.uszLor, U.uszXor, U.uszShl, U.uszShr] ]
  natCompare check gen
  errs <- readIORef check
  if null errs
    then putStrLn "proptests: all properties held"
    else do
      putStrLn ("proptests: " ++ show (length errs) ++ " failures; first 10:")
      mapM_ (putStrLn . ("  " ++)) (take 10 (reverse errs))
      exitFailure
