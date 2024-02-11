import Data.Void

type Neg p = p -> Void

ej_neg_7 :: (Neg q -> Neg p) -> (p -> Neg (Neg q))
ej_neg_7 h1 h2 h3 = (h1 h3) h2

-- λ> :t ej_neg_7
-- ej_neg_7 :: (Neg q -> Neg p) -> p -> Neg (Neg q)
