import Fusion
import Zempic.Nat
import System.Environment (getArgs)

main :: IO ()
main = do
  (w : n : _) <- getArgs
  let k = fromInteger (read n) :: ZNat
  print (if w == "fused" then z_pipeFused k else z_pipeLean k)
