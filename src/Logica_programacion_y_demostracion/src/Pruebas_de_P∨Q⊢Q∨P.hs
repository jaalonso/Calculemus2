orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h1 _  = h1 h
orElim (Right h) _  h2 = h2 h

ej_dis_4 :: Either p q -> Either q p
ej_dis_4 h = orElim h Right Left

ej_dis_4b :: Either p q -> Either q p
ej_dis_4b (Left  h) = Right h
ej_dis_4b (Right h) = Left h

-- λ> :t ej_dis_4
-- ej_dis_4 :: Either p q -> Either q p
-- λ> :t ej_dis_4b
-- ej_dis_4b :: Either p q -> Either q p
