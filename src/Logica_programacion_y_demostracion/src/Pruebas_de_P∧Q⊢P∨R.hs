ej_dis_2 :: (p,q) -> Either p r
ej_dis_2 h = Left (fst h)

ej_dis_2b :: (p,q) -> Either p r
ej_dis_2b (h,_) = Left h

-- λ> :t ej_dis_2
-- ej_dis_2 :: (p, q) -> Either p r
-- λ> :t ej_dis_2b
-- ej_dis_2b :: (p, q) -> Either p r
