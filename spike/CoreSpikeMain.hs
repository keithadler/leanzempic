import CoreSpike
import System.Environment (getArgs)

main :: IO ()
main = do
  [w, n] <- getArgs
  let k = read n
  print $ case w of
    "fact" -> z_fact k
    "sum" -> z_sumTo 0 k
    _ -> z_collatz 1000 k 0
