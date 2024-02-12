import Data.Void

type Neg p = p -> Void

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

ejemplo :: (Neg p -> q) -> Neg q -> p
ejemplo h1 h2 = byContradiction (h2 . h1)

-- λ> :t ejemplo
-- ejemplo :: (Neg p -> q) -> Neg q -> p
