import Data.Void

type Neg p = p -> Void

not_not_I :: p -> Neg (Neg p)
not_not_I h1 h2 = h2 h1

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

eliminacionDN :: Neg (Neg p) -> p
eliminacionDN h = byContradiction h

ejemplo :: p -> Neg (Neg (q, r)) -> (Neg (Neg p), r)
ejemplo h1 h2 = (not_not_I h1, snd (eliminacionDN h2))

-- λ> :t ejemplo
-- ejemplo :: p -> Neg (Neg (q, r)) -> (Neg (Neg p), r)
