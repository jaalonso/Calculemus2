ej_cond_5 :: (p -> q) -> (q -> r) -> (p -> r)
ej_cond_5 h1 h2 = h2 . h1

-- λ> :t ej_cond_5
-- ej_cond_5 :: (p -> q) -> (q -> r) -> p -> r
