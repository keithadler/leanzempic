
-- ADAPTER (pure): same loops as upstream main; the sum is the result.
def entry (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in *...n do
    for j in *...i do
      s := s + j.repr.length
  return s
