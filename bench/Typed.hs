{-# LANGUAGE BangPatterns #-}
-- Hand-written typed ceiling (NOT generated): same algorithms, Word, no Any.
import System.Environment
sumTo :: Word -> Word -> Word
sumTo !acc 0 = acc
sumTo !acc n = sumTo (acc + (n-1) + 1) (n-1)
collatz :: Word -> Word -> Word -> Word
collatz 0 _ !s = s
collatz f n !s | n <= 1 = s
               | even n = collatz (f-1) (n `div` 2) (s+1)
               | otherwise = collatz (f-1) (3*n+1) (s+1)
collatzAll :: Word -> Word -> Word
collatzAll 0 !a = a
collatzAll i !a = collatzAll (i-1) (a + collatz 1000 i 0)
main = do { [w] <- getArgs; print (case w of "0" -> sumTo 0 200000000; _ -> collatzAll 1000000 0) }
