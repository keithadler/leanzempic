import Bench
import Zempic.Nat
import System.Environment (getArgs)

main :: IO ()
main = do
  a <- getArgs
  let w = case a of (x:_) -> fromInteger (read x); _ -> 2 :: ZNat
  print (z_runBench w)
