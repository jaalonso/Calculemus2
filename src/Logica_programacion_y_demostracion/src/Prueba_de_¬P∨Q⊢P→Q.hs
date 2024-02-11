import Data.Void

type Neg p = p -> Void

orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h2 _  = h2 h
orElim (Right h) _  h3 = h3 h

ej_dis_6 :: Either (Neg p) q -> (p -> q)
ej_dis_6 h h1 = orElim h (\h2 -> absurd (h2 h1)) id
