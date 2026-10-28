import StringAliasing
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_forks, z_selfAppend, z_literal, z_growth, z_snapshot, z_sharedCompare]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
