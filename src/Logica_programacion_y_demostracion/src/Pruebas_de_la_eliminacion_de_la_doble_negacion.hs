import Data.Void

type Neg p = p -> Void

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

eliminacionDN :: Neg (Neg p) -> p
eliminacionDN h = byContradiction h

-- λ> :t eliminacionDN
-- eliminacionDN :: Neg (Neg p) -> p
