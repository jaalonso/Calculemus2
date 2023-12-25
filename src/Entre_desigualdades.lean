-- Entre_desigualdades.lean
-- En ℝ, x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, en ℝ, x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que
--    x ≤ y                                                          (1)
--    x ≠ y                                                          (2)
-- Entonces, se tiene x ≤ y (por (1)) y, para probar y ≰ x, supongamos
-- que y ≤ x. Por (1), se tiene que x = y, en contradicción con (2).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    have h4 : x = y := le_antisymm h1 h3
    show False
    exact h2 h4

-- 2ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    show False
    exact h2 (le_antisymm h1 h3)

-- 3ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 4ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 5ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
  fun ⟨h1, h2⟩ ↦ ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 6ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  use h1
  exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 7ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  use h1
  -- ¬y ≤ x
  contrapose! h2
  -- h2 : y ≤ x
  -- ⊢ x = y
  apply le_antisymm h1 h2

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
