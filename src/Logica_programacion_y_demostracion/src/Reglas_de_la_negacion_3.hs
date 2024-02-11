import Data.Void

type Neg p = p -> Void

ej_neg_2 :: Neg (p, Neg p)
ej_neg_2 h = snd h (fst h)

ej_neg_2b :: Neg (p, Neg p)
ej_neg_2b (h1, h2) = h2 h1

-- λ> :t ej_neg_2
-- ej_neg_2 :: Neg (p, Neg p)
-- λ> :t ej_neg_2b
-- ej_neg_2b :: Neg (p, Neg p)
