orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h2 _  = h2 h
orElim (Right h) _  h3 = h3 h
