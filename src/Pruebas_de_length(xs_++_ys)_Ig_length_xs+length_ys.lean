-- Pruebas_de_length(xs_++_ys)_Ig_length_xs+length_ys.lean
-- Pruebas de length(xs ++ ys) = length(xs) + length(ys)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean están definidas las funciones
--    length : list α → nat
--    (++)   : list α → list α → list α
-- tales que
-- + (length xs) es la longitud de xs. Por ejemplo,
--      length [2,3,5,3] = 4
-- + (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
--      [1,2] ++ [2,3,5,3] = [1,2,2,3,5,3]
-- Dichas funciones están caracterizadas por los siguientes lemas:
--    length_nil  : length [] = 0
--    length_cons : length (x :: xs) = length xs + 1
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que
--    length (xs ++ ys) = length xs + length ys
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en xs.
--
-- Caso base: Supongamos que xs = []. Entonces,
--    length (xs ++ ys) = length ([] ++ ys)
--                      = length ys
--                      = 0 + length ys
--                      = length [] + length ys
--                      = length xs + length ys
--
-- Paso de inducción: Supongamos que xs = a :: as y que se verifica la
-- hipótesis de inducción
--    length (as ++ ys) = length as + length ys                     (HI)
-- Entonces,
--    length (xs ++ ys) = length ((a :: as) ++ ys)
--                      = length (a :: (as ++ ys))
--                      = length (as ++ ys) + 1
--                      = (length as + length ys) + 1      [por HI]
--                      = (length as + 1) + length ys
--                      = length (a :: as) + length ys
--                      = length xs + length ys

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open List

variable {α : Type}
variable (xs ys : List α)

-- 1ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . calc length ([] ++ ys)
         = length ys
           := congr_arg length (nil_append ys)
       _ = 0 + length ys
           := (zero_add (length ys)).symm
       _ = length [] + length ys
           := congrArg (. + length ys) length_nil.symm
  . calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))
           := congr_arg length (cons_append a as ys)
       _ = length (as ++ ys) + 1
           := length_cons a (as ++ ys)
       _ = (length as + length ys) + 1
           := congrArg (. + 1) HI
       _ = (length as + 1) + length ys
           := (Nat.succ_add (length as) (length ys)).symm
       _ = length (a :: as) + length ys
           := congrArg (. + length ys) (length_cons a as).symm

-- 2ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . calc length ([] ++ ys)
         = length ys
           := by rw [nil_append]
       _ = 0 + length ys
           := (zero_add (length ys)).symm
       _ = length [] + length ys
           := by rw [length_nil]
  . calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))
           := by rw [cons_append]
       _ = length (as ++ ys) + 1
           := by rw [length_cons]
       _ = (length as + length ys) + 1
           := by rw [HI]
       _ = (length as + 1) + length ys
           := (Nat.succ_add (length as) (length ys)).symm
       _ = length (a :: as) + length ys
           := congrArg (. + length ys) (length_cons a as).symm

-- 3ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with _ as HI
  . simp only [nil_append, zero_add, length_nil]
  . simp only [cons_append, length_cons, HI, Nat.succ_add]

-- 4ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with _ as HI
  . simp
  . simp [HI, Nat.succ_add]

-- 5ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . simp
  . simp [HI] ; linarith

-- 6ª demostración
-- ===============

lemma longitud_conc_1 (xs ys : List α):
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | nil => calc
    length ([] ++ ys)
        = length ys
          := by rw [nil_append]
      _ = 0 + length ys
          := by rw [zero_add]
      _ = length [] + length ys
          := by rw [length_nil]
  | cons a as HI => calc
    length ((a :: as) ++ ys)
        = length (a :: (as ++ ys))
          := by rw [cons_append]
      _ = length (as ++ ys) + 1
          := by rw [length_cons]
      _ = (length as + length ys) + 1
          := by rw [HI]
      _ = (length as + 1) + length ys
          := (Nat.succ_add (length as) (length ys)).symm
      _ = length (a :: as) + length ys
          := by rw [length_cons]

-- 7ª demostración
-- ===============

lemma longitud_conc_2 (xs ys : List α):
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | nil          => simp
  | cons _ as HI => simp [HI, Nat.succ_add]

-- 9ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- HI : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [HI]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = Nat.succ (length as) + length ys
    rw [Nat.succ_add]

-- 10ª demostración
-- ================

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- HI : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [HI]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [Nat.succ_add]

-- 11ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as HI
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- HI : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [HI]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = Nat.succ (length as) + length ys
    linarith

-- 12ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
length_append xs ys

-- 13ª demostración
-- ===============

example :
  length (xs ++ ys) = length xs + length ys :=
by simp

-- Lemas usados
-- ============

-- variable (m n p : ℕ)
-- variable (x : α)
-- #check (Nat.succ_add n m : Nat.succ n + m = Nat.succ (n + m))
-- #check (cons_append x xs ys : (x :: xs) ++ ys = x :: (xs ++ ys))
-- #check (length_append xs ys : length (xs ++ ys) = length xs + length ys)
-- #check (length_cons x xs : length (x :: xs) = length xs + 1)
-- #check (length_nil : length [] = 0)
-- #check (nil_append xs : [] ++ xs = xs)
-- #check (zero_add n : 0 + n = n)
