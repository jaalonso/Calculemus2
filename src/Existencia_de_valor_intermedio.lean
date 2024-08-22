-- Existencia_de_valor_intermedio.lean
-- Hay algún número real entre 2 y 3.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que hay algún número real entre 2 y 3.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que 2 < 5/2 < 3, basta elegir 5/2.

-- Demostracione con Lean4
-- =======================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 :=
    by norm_num
  show ∃ x : ℝ, 2 < x ∧ x < 3
  exact Exists.intro (5 / 2) h

-- 2ª demostración
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 :=
    by norm_num
  show ∃ x : ℝ, 2 < x ∧ x < 3
  exact ⟨5 / 2, h⟩

-- 3ª demostración
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  norm_num

-- 4ª demostración
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩
