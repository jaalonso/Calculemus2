import Data.Void

type Neg p = p -> Void

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

reduccionAbsurso :: (Neg p -> Void) -> p
reduccionAbsurso h = byContradiction h

-- λ> :t eliminacionDN
-- eliminacionDN :: Neg (Neg p) -> p
