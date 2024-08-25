-- Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs.lean
-- Pruebas de take n xs ++ drop n xs = xs
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean están definidas las funciones
--    take : Nat → List α → Nat
--    drop : Nat → List α → Nat
--    (++) : List α → List α → List α
-- tales que
-- + (take n xs) es la lista formada por los n primeros elementos de
--   xs. Por ejemplo,
--      take 2 [3,5,1,9,7] = [3,5]
-- + (drop n xs) es la lista formada eliminando los n primeros elementos
--   de xs. Por ejemplo,
--      drop 2 [3,5,1,9,7] = [1,9,7]
-- + (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
--      [3,5] ++ [1,9,7] = [3,5,1,9,7]
-- Dichas funciones están caracterizadas por los siguientes lemas:
--    take_zero      : take 0 xs = []
--    take_nil       : take n [] = []
--    take_cons      : take (succ n) (x :: xs) = x :: take n xs
--    drop_zero      : drop 0 xs = xs
--    drop_nil       : drop n [] = []
--    drop_succ_cons : drop (n + 1) (x :: xs) = drop n xs
--    nil_append     : [] ++ ys = ys
--    cons_append    : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que
--    take n xs ++ drop n xs = xs
-- ---------------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- Tenemos que demostrar que
--    (∀ n)(∀ xs)[take n xs ++ drop n xs = xs]
-- Lo haremos por inducción sobre n.
--
-- Caso base: Sea n = 0. Tenemos que demostrar que
--    (∀ xs)[take n xs ++ drop n xs = xs]
-- Sea xs una lista cualquiera. Entonces
--    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
--                           = [] ++ xs
--                           = xs
--
-- Paso de inducción: Supongamos la hipótesis de inducción (HI):
--    (∀ xs)[take n xs ++ drop n xs = xs]
-- y tenemos que demostrar que
--    (∀ xs)[take (n+1) xs ++ drop (n+1) xs = xs]
-- Lo probaremos por casos según xs.
--
-- Primer caso: Supongamos que xs = []. Entonces,
--    take (n+1) xs ++ drop (n+1) xs = take (n+1) [] ++ drop (n+1) []
--                                   = [] ++ []
--                                   = []
--
-- Segundo caso:  Supongamos que xs = y :: ys. Entonces,
--    take (n+1) xs ++ drop (n+1) xs
--    = take (n+1) (y :: ys) ++ drop (n+1) (y :: ys)
--    = (y :: take n ys) ++ drop n ys
--    = y :: (take n ys ++ drop n ys)
--    = y :: ys                                          [por la HI]
--    = xs

-- Otra forma alternativa de demostrarlo es distinguiendo los tres casos
-- de la definición de take; que es
--    take n xs = [],             si n = 0
--              = [],             si n = m+1 y xs = []
--              = y :: take m ys, si n = m+1 y xs = y :: ys
--
-- Caso 1: Supongamos que n = 0. Entonces,
--    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
--                           = [] ++ xs
--                           = xs
--
-- Caso 2: Supongamos que n = m+1 y xs = []. Entonces,
--    take (m+1) xs ++ drop (m+1) xs = take (m+1) [] ++ drop (m+1) []
--                                   = [] ++ []
--                                   = []
--
-- Caso 3: Supongamos que n = m+1 y xs = y :: ys. Entonces,
--    take (m+1) xs ++ drop (m+1) xs
--    = take (m+1) (y :: ys) ++ drop (m+1) (y :: ys)
--    = (y :: take m ys) ++ drop m ys
--    = y :: (take m ys ++ drop m ys)
--    = y :: ys                       [por el Lema aplicado a m ys]
--    = xs

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.List.Basic
import Mathlib.Tactic
open List Nat

variable {α : Type}
variable (n : ℕ)
variable (x : α)
variable (xs : List α)

-- 1ª demostración
-- ===============

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n HI generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    calc take zero xs ++ drop zero xs
           = [] ++ xs                 := rfl
         _ = xs                       := rfl
  . -- n : ℕ
    -- HI : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      calc take (succ n) [] ++ drop (succ n) []
             = [] ++ [] := rfl
           _ = []       := by rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = (y :: take n ys) ++ drop n ys := rfl
        _ = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [HI]

-- 2ª demostración
-- ===============

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n HI generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    rfl
  . -- n : ℕ
    -- HI : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [HI]

-- 3ª demostración
-- ===============

lemma take_drop_1 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, xs =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    calc
      take 0 xs ++ drop 0 xs
        = [] ++ xs := rfl
      _ = xs       := rfl
  | n+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    calc
      take (n+1) [] ++ drop (n+1) []
        = [] ++ [] := rfl
      _ = []       := by rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
        = (y :: take n ys) ++ drop n ys := rfl
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_1 n ys]

-- 4ª demostración
-- ===============

lemma take_drop_2 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, _ =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    rfl
  | _+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_2 n ys]

-- 5ª demostración
-- ===============

lemma take_drop_3 : take n xs ++ drop n xs = xs :=
take_append_drop n xs
