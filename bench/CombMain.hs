import Combinators
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_t1, z_t2, z_t3, z_t4, z_t5, z_t6, z_all]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
