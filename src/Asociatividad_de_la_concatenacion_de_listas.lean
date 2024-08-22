-- Asociatividad_de_la_concatenacion_de_listas.lean
-- Asociatividad de la concatenación de listas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 la operación de concatenación de listas se representa por
-- (++) y está caracterizada por los siguientes lemas
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que la concatenación es asociativa; es decir,
--    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en xs.
--
-- Caso base: Supongamos que xs = [], entonces
--    xs ++ (ys ++ zs) = [] ++ (ys ++ zs)
--                     = ys ++ zs
--                     = ([] ++ ys) ++ zs
--                     = (xs ++ ys) ++ zs
--
-- Paso de inducción: Supongamos que xs = a :: as y la hipótesis de
-- inducción
--    as ++ (ys ++ zs) = (as ++ ys) + zs                            (HI)
-- Entonces
--    xs ++ (ys ++ zs) = (a :: as) ++ (ys ++ zs)
--                     = a :: (as ++ (ys ++ zs))
--                     = a :: ((as ++ ys) ++ zs)    [por HI]
--                     = (a :: (as ++ ys)) ++ zs
--                     = ((a :: as) ++ ys) ++ zs
--                     = (xs ++ ys) ++ zs

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (xs ys zs : List α)

-- 1ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := nil_append (ys ++ zs)
       _ = ([] ++ ys) ++ zs        := congrArg (. ++ zs) (nil_append ys).symm
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := cons_append a as (ys ++ zs)
       _ = a :: ((as ++ ys) ++ zs) := congrArg (a :: .) HI
       _ = (a :: (as ++ ys)) ++ zs := (cons_append a (as ++ ys) zs).symm

-- 2ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by rw [nil_append]
       _ = ([] ++ ys) ++ zs        := by rw [nil_append]
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := by rw [cons_append]
       _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
       _ = (a :: (as ++ ys)) ++ zs := by rw [cons_append]
       _ = ((a :: as) ++ ys) ++ zs := by rw [← cons_append]

-- 3ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by exact rfl
       _ = ([] ++ ys) ++ zs        := by exact rfl
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := rfl
       _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
       _ = (a :: (as ++ ys)) ++ zs := rfl
       _ = ((a :: as) ++ ys) ++ zs := rfl

-- 4ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by simp
       _ = ([] ++ ys) ++ zs        := by simp
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := by simp
       _ = a :: ((as ++ ys) ++ zs) := congrArg (a :: .) HI
       _ = (a :: (as ++ ys)) ++ zs := by simp
       _ = ((a :: as) ++ ys) ++ zs := by simp

-- 5ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as
  . simp
  . exact (append_assoc (a :: as) ys zs).symm

-- 6ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . -- ⊢ [] ++ (ys ++ zs) = ([] ++ ys) ++ zs
    rw [nil_append]
    -- ⊢ ys ++ zs = ([] ++ ys) ++ zs
    rw [nil_append]
  . -- a : α
    -- as : List α
    -- HI : as ++ (ys ++ zs) = as ++ ys ++ zs
    -- ⊢ (a :: as) ++ (ys ++ zs) = ((a :: as) ++ ys) ++ zs
    rw [cons_append]
    -- ⊢ a :: (as ++ (ys ++ zs)) = ((a :: as) ++ ys) ++ zs
    rw [HI]
    -- ⊢ a :: ((as ++ ys) ++ zs) = ((a :: as) ++ ys) ++ zs
    rw [cons_append]
    -- ⊢ a :: ((as ++ ys) ++ zs) = (a :: (as ++ ys)) ++ zs
    rw [cons_append]

-- 7ª demostración
-- ===============

lemma conc_asoc_1 (xs ys zs : List α) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction xs with
  | nil => calc
    [] ++ (ys ++ zs)
        = ys ++ zs         := by rw [nil_append]
      _ = ([] ++ ys) ++ zs := by rw [nil_append]
  | cons a as HI => calc
    (a :: as) ++ (ys ++ zs)
        = a :: (as ++ (ys ++ zs)) := by rw [cons_append]
      _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
      _ = (a :: (as ++ ys)) ++ zs := by rw [cons_append]
      _ = ((a :: as) ++ ys) ++ zs := congrArg (. ++ zs) (cons_append a as ys)

-- 8ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs  :=
(append_assoc xs ys zs).symm

-- 9ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by simp

-- Lemas usados
-- ============

-- variable (x : α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (cons_append x xs ys : (x :: xs) ++ ys = x :: (xs ++ ys))
-- #check (cons_inj x : x :: xs = x :: ys ↔ xs = ys)
-- #check (nil_append xs : [] ++ xs = xs)
