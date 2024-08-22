-- La_opuesta_es_no_monotona.lean
-- La función x ↦ -x no es monótona creciente.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la función opuesta no es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usando el lema del ejercicio anterior que afirma que una función f no
-- es monótona syss existen x e y tales que x ≤ y y f(x) > f(y), basta
-- demostrar que
--    (∃ x y)[x ≤ y ∧ -x > -y]
-- Basta elegir 2 y 3 ya que
--    2 ≤ 3 ∧ -2 > -3

-- Demostración con Lean4
-- ======================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import src.CNS_de_no_monotona

example : ¬Monotone fun x : ℝ ↦ -x :=
by
  apply not_Monotone_iff.mpr
  -- ⊢ ∃ x y, x ≤ y ∧ -x > -y
  use 2, 3
  -- ⊢ 2 ≤ 3 ∧ -2 > -3
  norm_num
