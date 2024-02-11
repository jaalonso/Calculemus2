import Data.Void

type Neg p = p -> Void

ej_neg_5 :: (p -> (q -> r)) -> p -> Neg r -> Neg q
ej_neg_5 h1 h2 h3 h4 = h3 (h1 h2 h4)

-- λ> :t ej_neg_5
-- ej_neg_5 :: (p -> q -> r) -> p -> Neg r -> Neg q
