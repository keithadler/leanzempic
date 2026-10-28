import Arrays
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_sieve, z_prefixSum, z_mapFold, z_rev, z_stack]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
