ej_conj_2 :: (p, q) -> (q, p)
ej_conj_2 = \ h -> (snd h, fst h)

ej_conj_2b :: (p, q) -> (q, p)
ej_conj_2b h = (snd h, fst h)

ej_conj_2c :: (p, q) -> (q, p)
ej_conj_2c = \ (hp, hq) -> (hq, hp)

ej_conj_2d :: (p, q) -> (q, p)
ej_conj_2d (hp, hq) = (hq, hp)

-- λ> :t ej_conj_2
-- ej_conj_2 :: (p, q) -> (q, p)
-- λ> :t ej_conj_2b
-- ej_conj_2b :: (p, q) -> (q, p)
-- λ> :t ej_conj_2c
-- ej_conj_2c :: (p, q) -> (q, p)
-- λ> :t ej_conj_2d
-- ej_conj_2d :: (p, q) -> (q, p)
