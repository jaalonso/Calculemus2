module Clase_2 where

import Data.Void

-- Reglas del condicional
-- ======================

ej_cond_1 :: (p -> q) -> p -> q
ej_cond_1 h1 h2 = h1 h2

ejercicio :: (p -> q) -> q -> p
ejercicio h1 h2 = undefined

ej_cond_2 :: p -> (p -> q) -> (p -> (q -> r)) -> r
ej_cond_2 h1 h2 h3 = (h3 h1) (h2 h1)

ej_cond_3 :: p -> p
ej_cond_3 = id

ej_cond_4 :: p -> (q -> p)
ej_cond_4 h _ = h

ej_cond_4b :: p -> (q -> p)
ej_cond_4b h1 _ = fst (h1,2020)

ej_cond_5 :: (p -> q) -> (q -> r) -> (p -> r)
ej_cond_5 h1 h2 = h2 . h1


-- Reglas de la conjunción
-- =======================

ej_conj_1 :: (p, q) -> r -> (q, r)
ej_conj_1 hpq hr = (snd hpq, hr)

ej_conj_1b :: (p, q) -> r -> (q, r)
ej_conj_1b (_, hq) hr = (hq, hr)

ej_conj_2 :: (p, q) -> (q, p)
ej_conj_2 = \ h -> (snd h, fst h)

ej_conj_2b :: (p, q) -> (q, p)
ej_conj_2b h = (snd h, fst h)

ej_conj_2c :: (p, q) -> (q, p)
ej_conj_2c = \ (hp, hq) -> (hq, hp)

ej_conj_2d :: (p, q) -> (q, p)
ej_conj_2d (hp, hq) = (hq, hp)

-- Reglas de la negación
-- =====================

falseElim :: Void -> a
falseElim = absurd

type Neg p = p -> Void

ej_neg_1 :: p -> Neg p -> Void
ej_neg_1 h1 h2 = h2 h1

ej_neg_2 :: Neg (p, Neg p)
ej_neg_2 h = snd h (fst h)

ej_neg_2b :: Neg (p, Neg p)
ej_neg_2b (h1, h2) = h2 h1

ej_neg_3 :: (p -> q) -> (p -> Neg q) -> Neg p
ej_neg_3 h1 h2 h = h2 h (h1 h)

ej_neg_4 :: (p -> q) -> (Neg q -> Neg p)
ej_neg_4 h1 h2 h3 = h2 (h1 h3)

ej_neg_4b :: (p -> q) -> (Neg q -> Neg p)
ej_neg_4b h1 h2 = h2 . h1

ej_neg_5 :: (p -> (q -> r)) -> p -> Neg r -> Neg q
ej_neg_5 h1 h2 h3 h4 = h3 (h1 h2 h4)

not_not_I :: p -> Neg (Neg p)
not_not_I h1 h2 = h2 h1

ej_neg_7 :: (Neg q -> Neg p) -> (p -> Neg (Neg q))
ej_neg_7 h1 h2 h3 = h1 h3 h2

-- Reglas de la disyunción
-- =======================

f :: Int -> Either Int Bool
f n | n >= 0    = Left  n
    | otherwise = Right False

-- λ> f 3
-- Left 3
-- λ> f (-3)
-- Right False

orInl :: p -> Either p q
orInl = Left

ej_dis_2 :: (p,q) -> Either p r
ej_dis_2 h1 = orInl (fst h1)

ej_dis_2b :: (p,q) -> Either p r
ej_dis_2b (h,_) = Left h

orInr :: q -> Either p q
orInr = Right

ej_dis_3 :: (p,q) -> Either r q
ej_dis_3 h1 = orInr (snd h1)

ej_dis_3b :: (p,q) -> Either r q
ej_dis_3b (_,h) = Right h

orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left  h) h2 _  = h2 h
orElim (Right h) _  h3 = h3 h

ej_dis_4 :: Either p q -> Either q p
ej_dis_4 h1 = orElim h1 orInr orInl

ej_dis_5 :: (q -> r) -> Either p q -> Either p  r
ej_dis_5 h1 h2 = orElim h2 orInl (orInr . h1)

ej_dis_6 :: Either (Neg p) q -> (p -> q)
ej_dis_6 h h1 = orElim h (\h2 -> falseElim (h2 h1)) id
