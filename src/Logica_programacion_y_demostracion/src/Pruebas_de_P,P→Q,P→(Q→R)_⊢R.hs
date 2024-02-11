ej_cond_2 :: p -> (p -> q) -> (p -> (q -> r)) -> r
ej_cond_2 h1 h2 h3 = (h3 h1) (h2 h1)

-- λ> :t ej_cond_2
-- ej_cond_2 :: p -> (p -> q) -> (p -> q -> r) -> r
