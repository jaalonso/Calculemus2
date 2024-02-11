ej_dis_3 :: (p,q) -> Either r q
ej_dis_3 h1 = Right (snd h1)

ej_dis_3b :: (p,q) -> Either r q
ej_dis_3b (_,h) = Right h

-- λ> :t ej_dis_3
-- ej_dis_3 :: (p, q) -> Either r q
-- λ> :t ej_dis_3b
-- ej_dis_3b :: (p, q) -> Either r q
