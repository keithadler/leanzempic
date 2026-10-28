import AesBench
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let seed = case rest of { (s : _) -> read s; [] -> 1 } :: Integer
  print (z_aesBench (fromInteger (read n)) (fromInteger seed) :: Natural)
