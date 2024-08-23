-- Divisor_del_mcd.lean
-- 3 divide al máximo común divisor de 6 y 15.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que 3 divide al máximo común divisor de 6 y 15.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    (∀ k, m, n ∈ ℕ)[k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n]
--
-- Por el lema,
--    3 ∣ gcd 6 15
-- se reduce a
--    3 ∣ 6 ∧ 3 ∣ 15
-- que se verifican fácilmente.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

-- 1ª demostración
-- ===============

example : 3 ∣ Nat.gcd 6 15 :=
by
  rw [dvd_gcd_iff]
  -- ⊢ 3 ∣ 6 ∧ 3 ∣ 15
  constructor
  . -- 3 ∣ 6
    norm_num
  . -- ⊢ 3 ∣ 15
    norm_num

-- 2ª demostración
-- ===============

example : 3 ∣ Nat.gcd 6 15 :=
by
  rw [dvd_gcd_iff]
  -- ⊢ 3 ∣ 6 ∧ 3 ∣ 15
  constructor <;> norm_num

-- Lemas usados
-- ============

-- variable (k m n : ℕ)
-- #check (dvd_gcd_iff : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n)
