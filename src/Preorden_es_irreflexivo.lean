-- Preorden_es_irreflexivo.lean
-- Si ≤ es un preorden, entonces < es irreflexiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si ≤ es un preorden, entonces < es irreflexiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará la siguiente propiedad de lo preórdenes
--    (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a]
-- Con dicha propiedad, lo que tenemos que demostrar se transforma en
--    ¬(a ≤ a ∧ a ≰ a)
-- Para demostrarla, supongamos que
--    a ≤ a ∧ a ≰ a
-- lo que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a : α)

-- 1ª demostración
-- ===============

example : ¬a < a :=
by
  rw [lt_iff_le_not_le]
  -- ⊢ ¬(a ≤ a ∧ ¬a ≤ a)
  rintro ⟨h1, h2⟩
  -- h1 : a ≤ a
  -- h2 : ¬a ≤ a
  -- ⊢ False
  exact h2 h1

-- 2ª demostración
-- ===============

example : ¬a < a :=
  irrefl a

-- Lemas usados
-- ============

-- variable (b : α)
-- #check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (irrefl a : ¬a < a)
