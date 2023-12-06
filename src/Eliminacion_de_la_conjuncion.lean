-- Eliminacion_de_la_conjuncion.lean
-- x ≤ y ∧ x ≠ y ⊢ y ≰ x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los reales, si
--    x ≤ y ∧ x ≠ y
-- entonces
--    ¬ y ≤ x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que y ≤ x. Entonces, por la antisimetría y la primera
-- parte de la hipótesis, se tiene que x = y que contradice la segunda
-- parte de la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  cases' h with h2 h3
  -- h2 : x ≤ y
  -- h3 : x ≠ y
  have h4 : x = y := le_antisymm h2 h1
  show False
  exact h3 h4

-- 2ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  have h4 : x = y := le_antisymm h.1 h1
  show False
  exact h.2 h4

-- 3ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h1
  show False
  exact h.2 (le_antisymm h.1 h1)

-- 4ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
fun h1 ↦ h.2 (le_antisymm h.1 h1)

-- 5ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  intro h'
  -- h' : y ≤ x
  -- ⊢ False
  apply h.right
  -- ⊢ x = y
  exact le_antisymm h.left h'

-- 6ª demostración
-- ===============

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
by
  cases' h with h1 h2
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  contrapose! h2
  -- h2 : y ≤ x
  -- ⊢ x = y
  exact le_antisymm h1 h2

-- 7ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩ h'
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  -- h' : y ≤ x
  -- ⊢ False
  exact h2 (le_antisymm h1 h')

-- 8ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
fun ⟨h1, h2⟩ h' ↦ h2 (le_antisymm h1 h')

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
