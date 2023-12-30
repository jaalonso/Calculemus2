-- CNS-de_no_monotona.lean
-- f: ℝ → ℝ no es monótona syss (∃x,y)[x ≤ y ∧ f(x) > f(y)]​.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-enero-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que f : ℝ → ℝ no es monótona syss existen x e y tales
-- que x ≤ y y f(x) > f(y).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de equivalencias:
--    f es no monótona ↔ ¬(∀ x y)[x ≤ y → f(x) ≤ f(y)]
--                     ↔ (∃ x y)[x ≤ y ∧ f(x) > f(y)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {f : ℝ → ℝ}

-- 1ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f y < f x  := by simp_all only [not_forall, not_le, exists_prop]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by rfl

-- 2ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by aesop

-- 3ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  push_neg
  -- ⊢ (Exists fun ⦃a⦄ => Exists fun ⦃b⦄ => a ≤ b ∧ f b < f a) ↔ ∃ x y, x ≤ y ∧ f x > f y
  rfl

-- 4ª demostración
-- ===============

lemma not_Monotone_iff :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  aesop
