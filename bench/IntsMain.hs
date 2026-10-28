import Ints
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_fnv, z_bytes, z_xorshift, z_convs, z_edges, z_chars]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
