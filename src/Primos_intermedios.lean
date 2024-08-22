-- Primos_intermedios.lean
-- Existen números primos m y n tales que 4 < m < n < 10.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que existen números primos m y n tales que
-- 4 < m < n < 10.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Basta considerar los números 5 y 7, ya que son primos y
-- 4 < 5 < 7 < 10.

-- Demostración con Lean4
-- ======================

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

example :
  ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n :=
by
  use 5, 7
  norm_num
