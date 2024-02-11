import Data.Void

type Neg p = p -> Void

ej_neg_4 :: (p -> q) -> (Neg q -> Neg p)
ej_neg_4 h1 h2 h3 = h2 (h1 h3)

ej_neg_4b :: (p -> q) -> (Neg q -> Neg p)
ej_neg_4b h1 h2 = h2 . h1

-- λ> :t ej_neg_4
-- ej_neg_4 :: (p -> q) -> Neg q -> Neg p
-- λ> :t ej_neg_4b
-- ej_neg_4b :: (p -> q) -> Neg q -> Neg p
