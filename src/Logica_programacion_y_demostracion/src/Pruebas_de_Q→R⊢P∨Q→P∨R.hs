orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h2 _  = h2 h
orElim (Right h) _  h3 = h3 h

ej_dis_5 :: (q -> r) -> Either p q -> Either p  r
ej_dis_5 h h1 = orElim h1 Left (Right . h)

-- λ> :t ej_dis_5
-- ej_dis_5 :: (q -> r) -> Either p q -> Either p r
