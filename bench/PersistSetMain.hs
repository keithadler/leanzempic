-- Persistent aSet microbenchmark for BENCH.md ("Persistent array undo records"): ghc -O2 -i../runtime PersistSetMain.hs; run with 40000.
{-# LANGUAGE BangPatterns #-}
import Zempic.Arr
import System.Environment
import Unsafe.Coerce
main = do
  [n] <- getArgs
  a0 <- aReplicate 1000 (unsafeCoerce (0::Int))
  let go !i !a | i == (read n :: Int) = return a
               | otherwise = aSet a (i `mod` 1000) (unsafeCoerce i) >>= go (i+1)
  a <- go 0 a0
  -- read an old version: reroot chain
  v <- aGet a0 5 (unsafeCoerce (0::Int))
  print (aLength a, (unsafeCoerce v :: Int))
