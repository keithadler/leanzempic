import Aliasing
import Numeric.Natural (Natural)
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : rest) <- getArgs
  let k = fromInteger (read n) :: Natural
      fs = [z_shared, z_twice, z_cow, z_mixedCallers, z_hold, z_closure, z_inList, z_nested, z_identity, z_branches, z_keepOld, z_swapShared, z_captureThenSet, z_storedThenSet, z_joined]
  case rest of
    (i : _) -> print ((fs !! read i) k)
    [] -> mapM_ (print . ($ k)) fs
