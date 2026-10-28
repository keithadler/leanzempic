import Arrays2
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_mixed, z_preds]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
