-- Pruebas_de_length_(replicaten x)_Ig_n.lean
-- Pruebas de length (replicate n x) = n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 están definidas las funciones length y replicate tales que
-- + (length xs) es la longitud de la lista xs. Por ejemplo,
--      length [1,2,5,2] = 4
-- + (replicate n x) es la lista que tiene el elemento x n veces. Por
--   ejemplo,
--      replicate 3 7 = [7, 7, 7]
--
-- Demostrar que
--    length (replicate n x) = n
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en n
--
-- Caso base:
--    length (replicate 0 x) = length []
--                           = 0
--
-- Paso de inducción: Se supone la hipótesis de inducción
--    length (replicate n x) = n                                    (HI)
-- Entonces,
--    length (replicate (n+1) x)
--    = length (x :: replicate n x)
--    = length (replicate n x) + 1
--    = n + 1                        [por la HI]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (x : α)
variable (n : ℕ)

-- 1ª demostración
-- ===============

example :
  length (replicate n x) = n :=
by
  induction n with
  | zero =>
    -- ⊢ (replicate 0 x).length = 0
    calc length (replicate 0 x)
          = length []                   := rfl
        _ = 0                           := length_nil
  | succ n HI =>
    -- n : ℕ
    -- HI : (replicate n x).length = n
    -- ⊢ (replicate (n + 1) x).length = n + 1
    calc length (replicate (n+1) x)
         = length (x :: replicate n x)  := by congr
       _ = length (replicate n x) + 1   := length_cons
       _ = n + 1                        := congrArg (. + 1) HI

-- 2ª demostración
-- ===============

example :
  length (replicate n x) = n :=
by
  induction n with
  | zero =>
    -- ⊢ (replicate 0 x).length = 0
    calc length (replicate 0 x)
          = length []                   := rfl
        _ = 0                           := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : (replicate n x).length = n
    -- ⊢ (replicate (n + 1) x).length = n + 1
    calc length (replicate (n+1) x)
         = length (x :: replicate n x)  := rfl
       _ = length (replicate n x) + 1   := rfl
       _ = n + 1                        := by rw [HI]

-- 3ª demostración
-- ===============

example : length (replicate n x) = n :=
by
  induction n with
  | zero => rfl
  | succ => simp

-- 4ª demostración
-- ===============

example : length (replicate n x) = n :=
by
  induction n with
  | zero => simp
  | succ => simp

-- 5ª demostración
-- ===============

example : length (replicate n x) = n :=
by induction n <;> simp [*]

-- 6ª demostración
-- ===============

example : length (replicate n x) = n :=
length_replicate

-- 7ª demostración
-- ===============

example : length (replicate n x) = n :=
by simp

-- 8ª demostración
-- ===============

lemma length_replicate_1 n (x : α) :
  length (replicate n x) = n :=
by
  induction n with
  | zero => calc
    length (replicate 0 x)
      = length ([] : List α)         := by simp only [replicate_zero]
    _ = 0                            := length_nil
  | succ n HI => calc
    length (replicate  (n + 1) x)
      = length (x :: replicate n x) := by simp only [replicate_succ]
    _ = length (replicate n x) + 1  := by simp only [length_cons]
    _ = n + 1                       := by simp only [HI]

-- 9ª demostración
-- ===============

lemma length_replicate_2 n (x : α) :
  length (replicate n x) = n :=
by induction n with
  | zero => calc
    length (replicate 0 x)
      = length ([] : List α)        := rfl
    _ = 0                           := rfl
  | succ n HI => calc
    length (replicate  (n + 1) x)
      = length (x :: replicate n x) := rfl
    _ = length (replicate n x) + 1  := rfl
    _ = n + 1                       := congrArg (. + 1) HI

-- 10ª demostración
-- ================

lemma length_replicate_3 n (x : α) :
  length (replicate n x) = n :=
by induction n with
  | zero      => simp
  | succ n HI => simp only [HI, replicate_succ, length_cons]

-- 11ª demostración
-- ===============

lemma length_replicate_4 :
  ∀ n, length (replicate n x) = n
| 0     => by simp
| (n+1) => by simp [*]

-- Lemas usados
-- ============

variable (xs : List α)
#check (length_cons : length (x :: xs) = length xs + 1)
#check (length_nil : length [] = 0)
#check (length_replicate : length (replicate n x) = n)
#check (replicate_succ : replicate (n + 1) x = x :: replicate n x)
#check (replicate_zero : replicate 0 x = [])
