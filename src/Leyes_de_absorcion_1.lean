-- Leyes_de_absorcion_1.lean
-- En los retículos, x ⊓ (x ⊔ y) = x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los retículos se verifica que
--    x ⊓ (x ⊔ y) = x
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración se usarán los siguientes lemas
--    le_antisymm  : x ≤ y → y ≤ x → x = y
--    inf_le_left  : x ⊓ y ≤ x
--    le_inf       : z ≤ x → z ≤ y → z ≤ x ⊓ y
--    le_rfl       : x ≤ x
--    le_sup_left  : x ≤ x ⊔ y
--
-- Por le_antisymm, basta demostrar las siguientes relaciones:
--    x ⊓ (x ⊔ y) ≤ x                                                (1)
--    x ≤ x ⊓ (x ⊔ y)                                                (2)
--
-- La (1) se tiene por inf_le_left.
--
-- Para demostrar la (2), por le_inf, basta probar las relaciones:
--    x ≤ x                                                         (2a)
--    x ≤ x ⊔ y                                                     (2b)
--
-- La (2a) se tiene por le_rfl.
--
-- La (2b) se tiene por le_sup_left

-- Demostraciones con Lean4
-- ========================

import Mathlib.Order.Lattice

variable {α : Type _} [Lattice α]
variable (x y : α)

-- 1ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  have h1 : x ⊓ (x ⊔ y) ≤ x := inf_le_left
  have h2 : x ≤ x ⊓ (x ⊔ y) := by
  { have h2a : x ≤ x := le_rfl
    have h2b : x ≤ x ⊔ y := le_sup_left
    show x ≤ x ⊓ (x ⊔ y)
    exact le_inf h2a h2b  }
  show x ⊓ (x ⊔ y) = x
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  have h1 : x ⊓ (x ⊔ y) ≤ x := by simp
  have h2 : x ≤ x ⊓ (x ⊔ y) := by simp
  show x ⊓ (x ⊔ y) = x
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  apply le_antisymm
  . -- x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . -- x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . -- x ≤ x
      apply le_rfl
    . -- x ≤ x ⊔ y
      apply le_sup_left

-- 4ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
le_antisymm inf_le_left (le_inf le_rfl le_sup_left)

-- 5ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
-- by apply?
inf_sup_self

-- 6ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by simp

-- Lemas usados
-- ============

-- variable (z : α)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_sup_self : x ⊓ (x ⊔ y) = x)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
-- #check (le_rfl : x ≤ x)
-- #check (le_sup_left : x ≤ x ⊔ y)
