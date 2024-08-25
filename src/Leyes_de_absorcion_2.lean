-- Leyes_de_absorcion_2.lean
-- En los retículos, x ⊔ (x ⊓ y) = x.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los retículos se verifica que
--    x ⊔ (x ⊓ y) = x
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración se usarán los siguientes lemas
--   le_antisymm  : x ≤ y → y ≤ x → x = y
--   inf_le_left  : x ⊓ y ≤ x
--   le_rfl       : x ≤ x
--   le_sup_left  : x ≤ x ⊔ y
--   sup_le       : x ≤ z → y ≤ z → x ⊔ y ≤ z
--
-- Por le_antisymm, basta demostrar las siguientes relaciones:
--    x ⊔ (x ⊓ y) ≤ x                                                (1)
--    x ≤ x ⊔ (x ⊓ y)    [que se tiene por le_sup_left]
--
-- Para demostrar (1), por sup_le, basta probar las relaciones:
--    x ≤ x              [que se tiene por le_rfl]
--    x ⊓ y ≤ x          [que se tiene por inf_le_left]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Order.Lattice

variable {α : Type _} [Lattice α]--
variable (x y : α)

-- 1ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  have h1 : x ⊔ (x ⊓ y) ≤ x := by
  { have h1a : x ≤ x := le_rfl
    have h1b : x ⊓ y ≤ x := inf_le_left
    show x ⊔ (x ⊓ y) ≤ x
    exact sup_le h1a h1b }
  have h2 : x ≤ x ⊔ (x ⊓ y) := le_sup_left
  show x ⊔ (x ⊓ y) = x
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  have h1 : x ⊔ (x ⊓ y) ≤ x := by simp
  have h2 : x ≤ x ⊔ (x ⊓ y) := by simp
  show x ⊔ (x ⊓ y) = x
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  apply le_antisymm
  . -- x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    . -- x ≤ x
      apply le_rfl
    . -- x ⊓ y ≤ x
      apply inf_le_left
  . -- x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by apply?
sup_inf_self

-- 5ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by simp

-- Lemas usados
-- ============

-- variable (z : α)
-- #check (le_rfl : x ≤ x)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (sup_inf_self : x ⊔ (x ⊓ y) = x)
