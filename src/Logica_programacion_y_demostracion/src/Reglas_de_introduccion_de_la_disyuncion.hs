orInl :: p -> Either p q
orInl = Left

orInr :: q -> Either p q
orInr = Right

-- λ> :t orInl
-- orInl :: p -> Either p q
-- λ> :t orInr
-- orInr :: q -> Either p q
