import Data.Void

falseElim :: Void -> a
falseElim = absurd

-- λ> :t falseElim
-- falseElim :: Void -> a
