import Data.Void

type Neg p = p -> Void

orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h2 _  = h2 h
orElim (Right h) _  h3 = h3 h

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

tercioExcluso :: Either p (Neg p)
tercioExcluso =  byContradiction (\h1-> h1 (Left (byContradiction (\h2 -> h1 (Right h2)))))

ejemplo :: (p -> q) -> Either (Neg p) q
ejemplo h = case tercioExcluso of
  Left p  -> Right (h p)
  Right q -> Left q
