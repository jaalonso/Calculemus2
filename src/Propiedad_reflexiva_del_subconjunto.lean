-- Propiedad_reflexiva_del_subconjunto.lean
-- Para cualquier conjunto s, s ⊆ s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para cualquier conjunto s, s ⊆ s.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x) [x ∈ s → × ∈ s]
-- Sea x tal que
--    x ∈ s                                                          (1)
-- Entonces, por (1), se tiene que
--    x ∈ s
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Tactic

variable {α : Type _}
variable (s : Set α)

-- 1ª demostración
example : s ⊆ s :=
by
  intro x xs
  exact xs

-- 2ª demostración
example : s ⊆ s :=
  fun (x : α) (xs : x ∈ s) ↦ xs

-- 3ª demostración
example : s ⊆ s :=
  fun _ xs ↦ xs

-- 4ª demostración
example : s ⊆ s :=
  -- by exact?
  rfl.subset

-- 5ª demostración
example : s ⊆ s :=
by rfl
