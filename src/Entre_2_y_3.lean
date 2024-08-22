-- Entre_2_y_3.lean
-- (∃x ∈ ℝ)[2 < x < 3]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que (∃x ∈ ℝ)[2 < x < 3]
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Podemos usar el número 5/2 y comprobar que 2 < 5/2 < 3.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  show 2 < 5 / 2 ∧ 5 / 2 < 3
  constructor
  . show 2 < 5 / 2
    norm_num
  . show 5 / 2 < 3
    norm_num

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  constructor
  . norm_num
  . norm_num

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  constructor <;> norm_num

-- 4ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5/2, by norm_num⟩
