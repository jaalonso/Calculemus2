import Data.Void

type Neg p = p -> Void

not_not_I :: p -> Neg (Neg p)
not_not_I h1 h2 = h2 h1

-- λ> :t not_not_I
-- not_not_I :: p -> Neg (Neg p)
