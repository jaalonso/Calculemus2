import Data.Void

type Neg p = p -> Void

ej_neg_1 :: p -> Neg p -> Void
ej_neg_1 h1 h2 = h2 h1

-- λ> :t ej_neg_1
-- ej_neg_1 :: p -> Neg p -> Void
