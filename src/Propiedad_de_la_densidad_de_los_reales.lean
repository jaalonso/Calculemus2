-- Propiedad_de_la_densidad_de_los_reales.lean
-- Si x, y ∈ ℝ tales que (∀ z)[y < z → x ≤ z], entonces x ≤ y
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean x, y números reales tales que
--    ∀ z, y < z → x ≤ z
-- Demostrar que x ≤ y.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostraremos por reducción al absurdo. Para ello, supongamos que
--    x ≰ y.
-- Entonces
--    y < x
-- y, por la densidad de ℝ, existe un a tal que
--    y < a < x
-- Puesto que y < a, por la hipótesis se tiene que
--    x ≤ a
-- en contradicción con
--    a < x.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  by_contra h1
  -- h1 : ¬x ≤ y
  -- ⊢ False
  have hxy : x > y := not_le.mp h1
  -- ⊢ ¬x > y
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  calc a
       < x := ha.2
     _ ≤ a := h a ha.1

-- 2ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  calc a
       < x := ha.2
     _ ≤ a := h a ha.1

-- 3ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  exact lt_of_lt_of_le ha.2 (h a ha.1)

-- 4ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1))

-- 5ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  rcases (exists_between hxy) with ⟨a, hya, hax⟩
  -- a : ℝ
  -- hya : y < a
  -- hax : a < x
  exact (lt_irrefl a) (lt_of_lt_of_le hax (h a hya))

-- 6ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_forall_le_of_dense h

-- Lemas usados
-- ============

-- variable (z : ℝ)
-- #check (exists_between : x < y → ∃ z, x < z ∧ z < y)
-- #check (le_of_forall_le_of_dense : (∀ z, y < z → x ≤ z) → x ≤ y)
-- #check (le_of_not_gt : ¬x > y → x ≤ y)
-- #check (lt_irrefl x : ¬x < x)
-- #check (lt_of_lt_of_le : x < y → y ≤ z → x < z)
-- #check (not_le : ¬x ≤ y ↔ y < x)
