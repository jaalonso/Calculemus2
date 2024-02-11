ej_conj_1 :: (p, q) -> r -> (q, r)
ej_conj_1 hpq hr = (snd hpq, hr)

-- λ> :t ej_conj_1
-- ej_conj_1 :: (p, q) -> r -> (q, r)
