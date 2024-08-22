-- Acotacion_del_valor_absoluto.lean
-- Si |x + 3| < 5, entonces -8 < x < 2.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    |x + 3| < 5
-- entonces
--    -8 < x < 2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que
--    |x + 3| < 5
-- entonces
--    -5 < x + 3 < 5
-- por tanto
--    -8 < x < 2

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  -- ⊢ -5 < x + 3 ∧ x + 3 < 5 → -8 < x ∧ x < 2
  intro h
  -- h : -5 < x + 3 ∧ x + 3 < 5
  -- ⊢ -8 < x ∧ x < 2
  constructor
  . -- ⊢ -8 < x
    linarith
  . -- x < 2
    linarith

-- 2ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  intro h
  constructor <;> linarith

-- Comentario: La composición (constructor <;> linarith) aplica constructor y a
-- continuación le aplica linarith a cada subojetivo.

-- 3ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  exact fun _ ↦ ⟨by linarith, by linarith⟩

-- Lemas usados
-- ============

-- #check (abs_lt: |x| < y ↔ -y < x ∧ x < y)
