import AutoFusion
import Zempic.Nat
import System.Environment (getArgs)

main :: IO ()
main = do
  (n : _) <- getArgs
  print (z_pipeAuto (fromInteger (read n) :: ZNat))
