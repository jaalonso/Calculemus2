import Data.Void

type Neg p = p -> Void

mt :: (p -> q) -> (Neg q -> Neg p)
mt h1 h2 = h2 . h1

not_not_I :: p -> Neg (Neg p)
not_not_I h1 h2 = h2 h1

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

eliminacionDN :: Neg (Neg p) -> p
eliminacionDN h = byContradiction h

ejemplo :: (q -> r) -> (Neg q -> Neg p) -> (p -> r)
ejemplo h1 h2 h3 = h1 (eliminacionDN (mt h2 (not_not_I h3)))

-- λ> :t ejemplo
-- ejemplo :: (q -> r) -> (Neg q -> Neg p) -> p -> r
