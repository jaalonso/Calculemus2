ej_cond_1 :: (p -> q) -> p -> q
ej_cond_1 h1 h2 = h1 h2

ej_cond_1' :: (p -> q) -> p -> q
ej_cond_1' = \ h1 h2 -> h1 h2

-- λ> :t ej_cond_1
-- ej_cond_1 :: (p -> q) -> p -> q
-- λ> :t ej_cond_1'
-- ej_cond_1' :: (p -> q) -> p -> q
