{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
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

-- * Hoisted buffers (Zempic.Arr, "Hoisted buffers")

-- | The raw-buffer operations of one element width.
data HOps t = HOps
  { hoistT :: A.Arr -> Maybe (A.HB t)
  , hGetT :: A.HB t -> Int -> t -> t
  , hSetT :: A.HB t -> A.Arr -> Int -> t -> A.Arr
  , hSwapT :: A.HB t -> A.Arr -> Int -> Int -> A.Arr
  , hPushT :: A.Arr -> t -> IO A.Arr }

-- | A loop that resolved the raw buffer once reads and writes exactly as a list model does, at every index
-- (negative, past the end, huge), and the buffer is only handed out for an array that is a plain live
-- buffer of the right kind: not a lazy handle, not an old version, not the source of a copy, not boxed.
arrHoisted :: forall t. (Integral t, Bounded t) => Check -> Gen -> HOps t -> Int -> Int -> Int -> IO ()
arrHoisted c g ops kind bits steps = do
  let label s = s ++ " (hoisted, " ++ show bits ++ " bits)"
      contents a = map (fromIntegral . (fromIntegral :: t -> Integer) . unsafeCoerce) <$> A.aToList a :: IO [Integer]
      mset k v m = take k m ++ [v] ++ drop (k + 1) m
      randV = do w <- next g
                 r <- below g 4
                 return (if r == 0 then toInteger (maxBound :: t) else toInteger (fromIntegral w :: t))
      idx m = do r <- below g 8
                 case r of
                   0 -> return (-1)
                   1 -> return (length m)
                   2 -> return maxBound
                   3 -> return minBound
                   _ -> below g (length m + 1)
      box :: Integer -> Any
      box v = unsafeCoerce (fromInteger v :: t)
  -- build a live array
  a0 <- A.aEmptyK kind 2
  let build a m 0 = return (a, m)
      build a m k = do v <- randV; a' <- hPushT ops a (fromInteger v); build a' (m ++ [v]) (k - 1 :: Int)
  n0 <- (+ 3) <$> below g 40
  (a, m0) <- build a0 [] n0
  case hoistT ops a of
    Nothing -> failWith c (label "a live buffer of its kind is not hoisted")
    Just hb -> do
      let go :: A.Arr -> [Integer] -> Int -> IO [Integer]
          go _ m 0 = return m
          go arr m k = do
            op <- below g 4
            i <- idx m
            j <- idx m
            v <- randV
            case op of
              0 -> do
                let want = if i >= 0 && i < length m then m !! i else v
                expect c (label "get") (toInteger (hGetT ops hb i (fromInteger v))) want
                when (i >= 0 && i < length m) $
                  expect c (label "get does not force the default in range") (toInteger (hGetT ops hb i (error "default forced"))) want
                go arr m (k - 1)
              1 -> do
                let r = hSetT ops hb arr i (fromInteger v)
                got <- contents r
                let m' = if i >= 0 && i < length m then mset i v m else m
                expect c (label "set") got m'
                go r m' (k - 1)
              _ -> do
                let r = hSwapT ops hb arr i j
                got <- contents r
                let m' = if i >= 0 && j >= 0 && i < length m && j < length m then mset j (m !! i) (mset i (m !! j) m) else m
                expect c (label "swap") got m'
                go r m' (k - 1)
      mEnd <- go a m0 steps
      gEnd <- contents a
      expect c (label "the array after the loop") gEnd mEnd
  -- not hoistable: a lazy handle (it copies at its first write), then a live buffer after that write
  h <- A.aShare a
  case hoistT ops h of
    Nothing -> return ()
    Just _ -> failWith c (label "a lazy handle is hoisted")
  h' <- A.aSetU h 0 (box 1)
  case hoistT ops h' of
    Nothing -> failWith c (label "the copy a lazy handle made is not hoisted")
    Just _ -> return ()
  -- not hoistable: an old version (a persistent write made it a diff)
  new <- A.aSet a 0 (box 5)
  case hoistT ops a of
    Nothing -> return ()
    Just _ -> failWith c (label "an old version is hoisted")
  case hoistT ops new of
    Nothing -> failWith c (label "the newest version is not hoisted")
    Just _ -> return ()
  -- not hoistable: the version a buffer copy was taken from (marked stale) -- grow a chain of persistent writes
  b0 <- A.aEmptyK kind 2
  (b, _) <- build b0 [] 4
  versions <- newIORef [b]
  let grow arr 0 = return arr
      grow arr k = do arr' <- A.aSet arr (k `mod` 4) (box (fromIntegral k)); modifyIORef versions (arr' :); grow arr' (k - 1 :: Int)
  _ <- grow b 400
  vs <- readIORef versions
  let hoisted = [ () | v <- vs, Just _ <- [hoistT ops v] ]
  expect c (label "of 401 versions along a chain with copies only the newest is hoisted") (length hoisted) 1
  -- not hoistable: a boxed buffer
  bx <- A.aEmptyK 0 2
  bx' <- A.aPush bx (box 3)
  case hoistT ops bx' of
    Nothing -> return ()
    Just _ -> failWith c (label "a boxed buffer is hoisted")

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

-- | Lazy copies (`aShare`): reading goes through to the source, the first write copies, and neither the
-- source nor another copy ever sees a write.
arrShared :: Check -> Gen -> Int -> IO ()
arrShared c g kind = do
  a0 <- A.aEmptyK kind 2
  n <- (+ 1) <$> below g 30
  vals <- replicateM n (below g (lim kind))
  base <- foldM (\x v -> A.aPush x (enc kind v)) a0 vals
  let mBase = map (norm kind) vals
  h1 <- A.aShare base
  h2 <- A.aShare h1                                   -- a chain of lazy handles
  g1 <- arrContents kind h1
  expect c "a lazy copy reads like its source" g1 mBase
  -- A persistent write to the source after sharing must not show through.
  src2 <- A.aSet base 0 (enc kind 1)
  g1b <- arrContents kind h1
  expect c "a later write to the source does not reach a lazy copy" g1b mBase
  g2 <- arrContents kind h2
  expect c "a lazy copy of a lazy copy" g2 mBase
  -- In-place writes on the copy copy first and leave everything else alone.
  (h1', m1) <- foldM (\(h, m) _ -> do
        op <- below g 4
        k <- subtract 1 <$> below g (length m + 3)
        v <- below g (lim kind)
        case op of
          0 -> do b <- A.aPushU h (enc kind v); return (b, m ++ [norm kind v])
          1 -> do b <- A.aPopU h; return (b, if null m then m else init m)
          2 -> do b <- A.aSetU h k (enc kind v); return (b, modelSet k (norm kind v) m)
          _ -> do
            j <- subtract 1 <$> below g (length m + 3)
            b <- A.aSwapU h k j
            return (b, modelSwap k j m)) (h1, mBase) [1 .. 12 :: Int]
  gw <- arrContents kind h1'
  expect c "in-place writes on a lazy copy" gw m1
  gsrc <- arrContents kind base
  expect c "the source is undisturbed by writes to its lazy copy" gsrc mBase
  gh2 <- arrContents kind h2
  expect c "a second lazy copy is undisturbed" gh2 mBase
  gs2 <- arrContents kind src2
  expect c "the source's own later version" gs2 (modelSet 0 (norm kind 1) mBase)

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

-- | Read an array whose elements are all `Word`s (a boxed buffer holding `Word` boxes, or a word
-- buffer) through the unboxed reader, past its end too.
wordContents :: A.Arr -> IO [Int]
wordContents a = mapM (\i -> fromIntegral <$> A.aGetW a i 0) [0 .. A.aLength a - 1]

-- | The `Word`-typed primitives (no box per element) against a list model: on a boxed buffer and a word
-- buffer, in place and on stale versions, reads past the end, ranges and element moves between arrays.
arrWord :: Check -> Gen -> Int -> Int -> IO ()
arrWord c g kind steps = do
  let w :: Int -> Word
      w = fromIntegral
  a0 <- A.aEmptyK kind 2
  (aEnd, mEnd) <- foldM
    (\(a, m) _ -> do
        op <- below g 5
        k <- subtract 1 <$> below g (length m + 3)
        v <- below g 1000
        (b, mb) <- case op of
          0 -> do b <- A.aPushUW a (w v); return (b, m ++ [v])
          1 -> do b <- A.aSetUW a k (w v); return (b, modelSet k v m)
          2 -> do b <- A.aPopU a; return (b, if null m then m else init m)
          3 -> do
            j <- subtract 1 <$> below g (length m + 3)
            useW <- below g 2
            b <- if useW == 0 then A.aSwapU a k j else A.aSwapUW a k j
            return (b, modelSwap k j m)
          _ -> do
            r <- A.aGetW a k 77
            expect c "aGetW" (fromIntegral r) (if k >= 0 && k < length m then m !! k else 77)
            rI <- evaluate (A.aGetWI a k 78)
            expect c "aGetWI" (fromIntegral rI) (if k >= 0 && k < length m then m !! k else 78)
            return (a, m)
        got <- wordContents b
        expect c ("word ops, kind " ++ show kind) got mb
        return (b, mb))
    (a0, []) [1 .. steps]
  -- A stale version falls back to the persistent operation.
  newer <- A.aPush aEnd (unsafeCoerce (4242 :: Word))
  s1 <- A.aPushUW aEnd 7
  gs1 <- wordContents s1
  expect c "stale word push falls back" gs1 (mEnd ++ [7])
  s2 <- A.aSetUW aEnd 0 9
  gs2 <- wordContents s2
  expect c "stale word set falls back" gs2 (modelSet 0 9 mEnd)
  gn <- wordContents newer
  expect c "the newer version is undisturbed" gn (mEnd ++ [4242])
  g0 <- wordContents aEnd
  expect c "the stale version is undisturbed" g0 mEnd

-- | The narrow-typed primitives (`UInt8/16/32/64` elements read and written with no box), against a list
-- model: on a boxed buffer and a buffer of the matching kind, in place, through a lazy handle, on stale
-- versions (which must fall back), and with reads and writes past either end, at huge and negative indices.
data NOps t = NOps
  { nPushU :: A.Arr -> t -> IO A.Arr, nSetU :: A.Arr -> Int -> t -> IO A.Arr
  , nGetP :: A.Arr -> Int -> t -> t, nGetPS :: A.Arr -> Int -> t -> t, nSwapU :: A.Arr -> Int -> Int -> IO A.Arr }

arrNarrow :: forall t. (Integral t, Bounded t) => Check -> Gen -> NOps t -> Int -> Int -> Int -> IO ()
arrNarrow c g ops kind bits steps = do
  let toT :: Integer -> t
      toT = fromInteger
      box :: Integer -> Any
      box v = case bits of
        8 -> unsafeCoerce (fromInteger v :: Word8)
        16 -> unsafeCoerce (fromInteger v :: Word16)
        32 -> unsafeCoerce (fromInteger v :: Word32)
        _ -> unsafeCoerce (fromInteger v :: Word64)
      unbox :: Any -> Integer
      unbox a = case bits of
        8 -> toInteger (unsafeCoerce a :: Word8)
        16 -> toInteger (unsafeCoerce a :: Word16)
        32 -> toInteger (unsafeCoerce a :: Word32)
        _ -> toInteger (unsafeCoerce a :: Word64)
      randV = do w <- next g
                 r <- below g 4
                 return (if r == 0 then toInteger (maxBound :: t) else toInteger (fromIntegral w :: t))
      mset k v m = if k < 0 || k >= length m then m else take k m ++ [v] ++ drop (k + 1) m
      mswap i j m = if i < 0 || j < 0 || i >= length m || j >= length m then m else mset j (m !! i) (mset i (m !! j) m)
      contents a = map unbox <$> A.aToList a
      label s = s ++ " (" ++ show bits ++ " bits, kind " ++ show kind ++ ")"
      idx m = do r <- below g 8
                 case r of
                   0 -> return (-1)
                   1 -> return (length m)
                   2 -> return maxBound
                   3 -> return minBound
                   _ -> below g (length m + 1)
  a0 <- A.aEmptyK kind 2
  (aEnd, mEnd) <- foldM
    (\(a, m) _ -> do
        op <- below g 7
        k <- idx m
        v <- randV
        (b, mb) <- case op of
          0 -> do b <- nPushU ops a (toT v); return (b, m ++ [v])
          1 -> do b <- nSetU ops a k (toT v); return (b, mset k v m)
          2 -> do b <- A.aPopU a; return (b, if null m then m else init m)
          3 -> do
            j <- idx m
            b <- nSwapU ops a k j
            return (b, mswap k j m)
          4 -> do
            let want = if k >= 0 && k < length m then m !! k else v
            expect c (label "narrow get") (toInteger (nGetPS ops a k (toT v))) want
            expect c (label "narrow get, lazy default") (toInteger (nGetP ops a k (toT v))) want
            -- an in-range read must not force its default (the compiled code passes a shared error value)
            when (k >= 0 && k < length m) $
              expect c (label "narrow get does not force the default in range") (toInteger (nGetP ops a k (error "default forced"))) (m !! k)
            return (a, m)
          5 -> do
            -- a lazily shared handle copies on its first write and leaves the source alone
            h <- A.aShare a
            h' <- nSetU ops h 0 (toT v)
            gsrc <- contents a
            expect c (label "source undisturbed by a write to its lazy copy") gsrc m
            return (h', mset 0 v m)
          _ -> do
            -- a persistent write first: the in-place ones must keep working on the new live version
            b <- A.aPush a (box v)
            return (b, m ++ [v])
        got <- contents b
        expect c (label "narrow ops") got mb
        return (b, mb))
    (a0, []) [1 .. steps]
  -- Stale versions fall back to the persistent operations.
  newer <- A.aPush aEnd (box 42)
  s1 <- nPushU ops aEnd (toT 7)
  gs1 <- contents s1
  expect c (label "stale narrow push falls back") gs1 (mEnd ++ [7])
  s2 <- nSetU ops aEnd 0 (toT 9)
  gs2 <- contents s2
  expect c (label "stale narrow set falls back") gs2 (mset 0 9 mEnd)
  s3 <- nSwapU ops aEnd 0 (length mEnd - 1)
  gs3 <- contents s3
  expect c (label "stale narrow swap falls back") gs3 (mswap 0 (length mEnd - 1) mEnd)
  gn <- contents newer
  expect c (label "the newer version is undisturbed") gn (mEnd ++ [42])
  g0 <- contents aEnd
  expect c (label "the stale version is undisturbed") g0 mEnd
  -- the compiled-code wrappers (word mode and exact mode) at indices no clamp may wrap around
  when (bits == 32) $ do
    let anyA = unsafeCoerce aEnd :: Any
        wantAt i = if i < length mEnd then toInteger (mEnd !! i) else 5
    forM_ [0 .. length mEnd + 1] $ \i -> do
      expect c "W.arrGetD32" (toInteger (W.arrGetD32 undefined 5 anyA (fromIntegral i))) (wantAt i)
      expect c "E.arrGetD32" (toInteger (E.arrGetD32 undefined 5 anyA (fromIntegral i))) (wantAt i)
    forM_ [2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1 :: Word] $ \i ->
      expect c "W.arrGetD32 at a huge index" (W.arrGetD32 undefined 5 anyA i) 5
    forM_ [2 ^ 64, 2 ^ 64 + 3, 2 ^ 70 :: Natural] $ \i ->
      expect c "E.arrGetD32 at a huge index" (E.arrGetD32 undefined 5 anyA i) 5

-- | `Array.range` and the element move behind `Array.append` / `Array.extract`.
arrRangeMove :: Check -> Gen -> IO ()
arrRangeMove c g = do
  n <- below g 40
  r <- A.aRangeW n
  gr <- wordContents r
  expect c "range" gr [0 .. n - 1]
  r2 <- A.aPushUW r 99
  gr2 <- wordContents r2
  expect c "push after range" gr2 ([0 .. n - 1] ++ [99])
  -- Moving elements from a source into a destination of the same or another kind.
  forM_ [(d, s) | d <- [0 .. 6], s <- [0 .. 6], d == s || (d, s) `elem` [(0, 5), (5, 0)]] $ \(dk, sk) -> do
    let lm = min (lim dk) (lim sk)
    vals <- replicateM (n + 1) (below g lm)
    s0 <- A.aEmptyK sk 2
    src <- foldM (\x v -> A.aPush x (enc' sk v)) s0 vals
    d0 <- A.aEmptyK dk 2
    m0 <- replicateM 3 (below g lm)
    dst0 <- foldM (\x v -> A.aPush x (enc' dk v)) d0 m0
    idxs <- replicateM 20 (below g (length vals))
    (dst, md) <- foldM (\(x, m) i -> do b <- A.aPushFromU x src i; return (b, m ++ [vals !! i])) (dst0, m0) idxs
    got <- mapM (\i -> dec' dk <$> A.aGet dst i (error "range")) [0 .. A.aLength dst - 1]
    expect c ("move kind " ++ show sk ++ " to " ++ show dk) got md
    gsrc <- mapM (\i -> dec' sk <$> A.aGet src i (error "range")) [0 .. A.aLength src - 1]
    expect c "move leaves its source alone" gsrc vals
  -- A `Word` written through a view as another element type: the buffer becomes boxed unless it holds
  -- `Word`s already, and every element then reads back as the new value.
  forM_ [0 .. 6] $ \kind -> do
    vals <- replicateM (n + 1) (below g (lim kind))
    e0 <- A.aEmptyK kind 2
    a <- foldM (\x v -> A.aPush x (enc kind v)) e0 vals
    new <- replicateM (n + 1) (below g 100000)
    a' <- foldM (\x (i, v) -> A.aSetUWB x i (fromIntegral v)) a (zip [0 ..] new)
    got <- wordContents a'
    expect c ("retyping write over kind " ++ show kind) got new
  where
    -- Kind 5 and kind 0 hold `Word`s in the cross-kind moves; the other kinds use `enc`/`dec`.
    enc' k v = if k == 0 then unsafeCoerce (fromIntegral v :: Word) else enc k v
    dec' k a = if k == 0 then fromIntegral (unsafeCoerce a :: Word) else dec k a

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

-- | The Word-element variants (word-mode Nat arrays), on an unboxed kind-5 buffer and on a boxed one,
-- against the model: single owner, a lazily shared handle, and stale versions (which must fall back).
arrWordShare :: Check -> Gen -> Int -> Int -> IO ()
arrWordShare c g kind steps = do
  let rd a i = A.aGetW a i 999999
      allOf a n = mapM (\i -> fromIntegral <$> rd a i) [0 .. n - 1] :: IO [Int]
  a0 <- A.aEmptyK kind 2
  (aEnd, mEnd) <- foldM
    (\(a, m) _ -> do
        op <- below g 3
        k <- subtract 1 <$> below g (length m + 3)
        v <- below g 1000
        (b, mb) <- case op of
          0 -> do b <- A.aPushUW a (fromIntegral v); return (b, m ++ [v])
          1 -> do b <- A.aSetUW a k (fromIntegral v); return (b, modelSet k v m)
          _ -> do
            b <- if null m then return a else A.aShare a   -- a lazy handle copies on its first write
            b' <- A.aSetUW b 0 5
            return (b', if null m then m else modelSet 0 5 m)
        got <- allOf b (length mb)
        expect c ("word in-place result, kind " ++ show kind) got mb
        oob <- rd b (length mb)
        expect c "word read past the end gives the default" oob 999999
        neg <- rd b (-1)
        expect c "word read at -1 gives the default" neg 999999
        gl <- A.aToList b
        expect c "word ops agree with the boxed view" (map (dec 5) gl) mb
        return (b, mb))
    (a0, []) [1 .. steps]
  -- A version whose buffer was copied away (count -1) must not be trusted as sole owner: two in-place
  -- pushes onto it have to stay apart.
  base <- foldM (\a i -> A.aPush a (enc 5 i)) a0 [1 .. 3 :: Int]
  let build (a, ms) i = do b <- A.aSet a 0 (enc 5 i); return (b, ms ++ [b])
  (_, versions) <- foldM build (base, [base]) [1 .. 80 :: Int]
  forM_ (reverse (drop 40 (take 80 versions))) $ \v -> do
    n <- return (A.aLength v)
    r1 <- A.aPushUW v 111
    r2 <- A.aPushUW v 222
    x1 <- allOf r1 (n + 1)
    x2 <- allOf r2 (n + 1)
    expect c "copied-away version: first in-place push survives the second" (last x1) 111
    expect c "copied-away version: second in-place push" (last x2) 222
  newer <- A.aPush aEnd (enc 5 4242)
  stale1 <- A.aPushUW aEnd 7
  gs <- allOf stale1 (length mEnd + 1)
  expect c "stale word push falls back" gs (mEnd ++ [7])
  stale2 <- A.aSetUW aEnd 0 9
  g2 <- allOf stale2 (length mEnd)
  expect c "stale word set falls back" g2 (modelSet 0 9 mEnd)
  gn <- allOf newer (length mEnd + 1)
  expect c "newer version undisturbed by stale word ops" gn (mEnd ++ [4242])
  g0 <- allOf aEnd (length mEnd)
  expect c "stale version itself undisturbed (word ops)" g0 mEnd

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

-- | The exact path's inlined small-operand cases (Natural's NS constructor) against Integer, with operands
-- on both sides of 2^64 (NS and NB mixed) and results that cross it, comparisons included.
natExactBig :: Check -> Gen -> IO ()
natExactBig c g = do
  let two64 = 2 ^ (64 :: Int) :: Integer
      pts = concat [[k - 1, k, k + 1] | k <- [0, 1, two64 - 1, two64, two64 * two64 - 1, two64 * two64]]
      ops :: [(String, Natural -> Natural -> Natural, Integer -> Integer -> Integer)]
      ops = [ ("add", E.natAdd, (+)), ("mul", E.natMul, (*)), ("sub", E.natSub, \a b -> max 0 (a - b))
            , ("div", E.natDiv, \a b -> if b == 0 then 0 else a `div` b)
            , ("mod", E.natMod, \a b -> if b == 0 then a else a `mod` b) ]
      rel :: [(String, Natural -> Natural -> Bool, Integer -> Integer -> Bool)]
      rel = [("eq", E.natEq, (==)), ("lt", E.natLt, (<)), ("le", E.natLe, (<=))]
      pickBig = do
        k <- below g 4
        if k == 0 then pick g (filter (>= 0) pts)
        else if k == 1 then (`mod` two64) . toInteger <$> next g
        else do x <- next g; y <- next g; z <- next g
                return ((toInteger x * two64 + toInteger y) * (if k == 2 then 1 else two64) + toInteger z `mod` 7)
  forM_ [1 .. 4000 :: Int] $ \_ -> do
    a <- pickBig
    b <- pickBig
    forM_ ops $ \(name, ef, ref) ->
      expect c ("exactbig." ++ name ++ " " ++ show a ++ " " ++ show b) (toInteger (ef (fromInteger a) (fromInteger b))) (ref a b)
    forM_ rel $ \(name, ef, ref) ->
      expect c ("exactbig." ++ name ++ " " ++ show a ++ " " ++ show b) (fromEnum (ef (fromInteger a) (fromInteger b))) (fromEnum (ref a b))
    -- A result that crosses 2^64 must still compare equal to the same value built another way.
    let s = E.natAdd (fromInteger a) (fromInteger b)
    expect c "exactbig.norm" (fromEnum (E.natEq s (fromInteger (a + b)))) 1

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
      when (kind == 5 || kind == 0) $ arrWordShare check gen kind 400
      arrShared check gen kind
      when (kind == 0 || kind == 5) $ arrWord check gen kind 400
      when (kind /= 0) $ arrPlaceholderRaw check gen kind
    arrRangeMove check gen
    natExactBig check gen
    arrHoisted check gen (HOps (\a -> A.aHoist8 a Just Nothing) A.hGetD8 (\b a i v -> A.hSet b a i v) (\b a i j -> A.hSwap b a i j) A.aPushU8) 1 8 400
    arrHoisted check gen (HOps (\a -> A.aHoist16 a Just Nothing) A.hGetD16 (\b a i v -> A.hSet b a i v) (\b a i j -> A.hSwap b a i j) A.aPushU16) 2 16 400
    arrHoisted check gen (HOps (\a -> A.aHoist32 a Just Nothing) A.hGetD32 (\b a i v -> A.hSet b a i v) (\b a i j -> A.hSwap b a i j) A.aPushU32) 3 32 400
    arrHoisted check gen (HOps (\a -> A.aHoist64 a Just Nothing) A.hGetD64 (\b a i v -> A.hSet b a i v) (\b a i j -> A.hSwap b a i j) A.aPushU64) 4 64 400
    forM_ [(0, 8), (1, 8), (0, 16), (2, 16), (0, 32), (3, 32), (0, 64), (4, 64)] $ \(kind, bits) ->
      case bits :: Int of
        8 -> arrNarrow check gen (NOps A.aPushU8 A.aSetU8 A.aGetP8 A.aGetPS8 A.aSwapU8) kind bits 300
        16 -> arrNarrow check gen (NOps A.aPushU16 A.aSetU16 A.aGetP16 A.aGetPS16 A.aSwapU16) kind bits 300
        32 -> arrNarrow check gen (NOps A.aPushU32 A.aSetU32 A.aGetP32 A.aGetPS32 A.aSwapU32) kind bits 300
        _ -> arrNarrow check gen (NOps A.aPushU64 A.aSetU64 A.aGetP64 A.aGetPS64 A.aSwapU64) kind bits 300
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
