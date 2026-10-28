import Examples
import Numeric.Natural (Natural)

main :: IO ()
main = do
  print (z_fact 20)
  print (z_sumTo 0 10000000)
  print (z_collatz 1000 27 0)
