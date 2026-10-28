import Bench
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  a <- getArgs
  let w = case a of (x:_) -> fromInteger (read x); _ -> 2 :: Natural
  print (z_runBench w)
