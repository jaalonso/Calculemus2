import Data.Void

type Neg p = p -> Void

byContradiction :: (Neg p -> Void) -> p
byContradiction = undefined

tercioExcluso :: Either p (Neg p)
tercioExcluso =  byContradiction (\h1-> h1 (Left (byContradiction (\h2 -> h1 (Right h2)))))

-- λ> :t tercioExcluso
-- tercioExcluso :: Either p (Neg p)
