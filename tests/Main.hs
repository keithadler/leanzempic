import Examples
import Zempic.Runtime
import Numeric.Natural (Natural)

n :: Integer -> Any
n = zo . (fromInteger :: Integer -> Natural)

main :: IO ()
main = do
  print (zu (z_fact (n 20)) :: Natural)
  print (zu (z_sumTo (n 0) (n 10000000)) :: Natural)
  let l = zo' [1 .. 5 :: Natural]
  print (zu (z_collatz (n 1000) (n 27) (n 0)) :: Natural)
  where zo' = foldr (\x acc -> zo (ZC_List_cons (zo x) acc)) (zo ZC_List_nil)
