import Examples
import Numeric.Natural (Natural)

main :: IO ()
main = do
  print (z_fact 20)
  print (z_sumTo 0 10000000)
  print (z_collatz 1000 27 0)
  print (z_fact 25) -- overflows 64 bits: must fall back to exact
