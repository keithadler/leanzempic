import BigNum
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  a <- getArgs
  let w = case a of (x:_) -> fromInteger (read x); _ -> 0 :: Natural
      s = case a of (_:y:_) -> fromInteger (read y); _ -> 100 :: Natural
  print (z_runBig w s)
