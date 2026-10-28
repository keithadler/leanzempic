import Bench
import Zempic.Runtime
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  a <- getArgs
  let w = case a of (x:_) -> read x; _ -> 2 :: Natural
  print (zu (z_runBench (zo w)) :: Natural)
