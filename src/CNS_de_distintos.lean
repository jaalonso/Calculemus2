-- CNS_de_distintos.lean
-- En ℝ, si x ≤ y, entonces y ≰ x ↔ x ≠ y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean x, y números reales tales que x ≤ y. Entonces, y ≰ x ↔ x ≠ y.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrar la equivalencia, demostraremos cada una de las
-- implicaciones.
--
-- Para demostrar la primera, supongamos que y ≰ x y que x =
-- y. Entonces, y ≤ x que es una contradicción.
--
-- Para demostrar la segunda, supongamos que x ≠ y y que y ≤
-- x. Entonces, por la hipótesis y la antisimetría, se tiene que x = y
-- lo que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . show ¬y ≤ x → x ≠ y
    { intro h1
      -- h1 : ¬y ≤ x
      -- ⊢ x ≠ y
      intro h2
      -- h2 : x = y
      -- ⊢ False
      have h3 : y ≤ x := by rw [h2]
      show False
      exact h1 h3 }
  . show x ≠ y → ¬y ≤ x
    { intro h1
      -- h1 : x ≠ y
      -- ⊢ ¬y ≤ x
      intro h2
      -- h2 : y ≤ x
      -- ⊢ False
      have h3 : x = y := le_antisymm h h2
      show False
      exact h1 h3 }

-- 2ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . show ¬y ≤ x → x ≠ y
    { intro h1
      -- h1 : ¬y ≤ x
      -- ⊢ x ≠ y
      intro h2
      -- h2 : x = y
      -- ⊢ False
      show False
      exact h1 (by rw [h2]) }
  . show x ≠ y → ¬y ≤ x
    { intro h1
      -- h1 : x ≠ y
      -- ⊢ ¬y ≤ x
      intro h2
      -- h2 : y ≤ x
      -- ⊢ False
      show False
      exact h1 (le_antisymm h h2) }

-- 3ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . show ¬y ≤ x → x ≠ y
    { intro h1 h2
      exact h1 (by rw [h2]) }
  . show x ≠ y → ¬y ≤ x
    { intro h1 h2
      exact h1 (le_antisymm h h2) }

-- 4ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . intro h1 h2
    exact h1 (by rw [h2])
  . intro h1 h2
    exact h1 (le_antisymm h h2)

-- 5ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . exact fun h1 h2 ↦ h1 (by rw [h2])
  . exact fun h1 h2 ↦ h1 (le_antisymm h h2)

-- 6ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h1 h2 ↦ h1 (by rw [h2]),
   fun h1 h2 ↦ h1 (le_antisymm h h2)⟩

-- 7ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  . show ¬y ≤ x → x ≠ y
    { intro h1
      -- h1 : ¬y ≤ x
      -- ⊢ x ≠ y
      contrapose! h1
      -- h1 : x = y
      -- ⊢ y ≤ x
      calc y = x := h1.symm
           _ ≤ x := by rfl }
  . show x ≠ y → ¬y ≤ x
    { intro h2
      -- h2 : x ≠ y
      -- ⊢ ¬y ≤ x
      contrapose! h2
      -- h2 : y ≤ x
      -- ⊢ x = y
      show x = y
      exact le_antisymm h h2 }

-- 8ª demostración
-- ===============

example
  (h : x ≤ y)
  : ¬y ≤ x ↔ x ≠ y :=
by
  constructor
  · -- ⊢ ¬y ≤ x → x ≠ y
    contrapose!
    -- ⊢ x = y → y ≤ x
    rintro rfl
    -- ⊢ x ≤ x
    rfl
  . -- ⊢ x ≠ y → ¬y ≤ x
    contrapose!
    -- ⊢ y ≤ x → x = y
    exact le_antisymm h
