import Data.Void

type Neg p = p -> Void

ej_neg_3 :: (p -> q) -> (p -> Neg q) -> Neg p
ej_neg_3 h1 h2 = \ h3 -> (h2 h3) (h1 h3)

ej_neg_3b :: (p -> q) -> (p -> Neg q) -> Neg p
ej_neg_3b h1 h2 h3 = (h2 h3) (h1 h3)

-- λ> :t ej_neg_3
-- ej_neg_3 :: (p -> q) -> (p -> Neg q) -> Neg p
-- λ> :t ej_neg_3b
-- ej_neg_3b :: (p -> q) -> (p -> Neg q) -> Neg p
