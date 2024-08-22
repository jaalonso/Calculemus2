-- Asociatividad_del_supremo.lean
-- En los retículos, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los retículos se verifica que
--    (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración se usarán los siguientes lemas
--    le_antisymm  : x ≤ y → y ≤ x → x = y
--    le_sup_left  : x ≤ x ⊔ y
--    le_sup_right : y ≤ x ⊔ y
--    sup_le       : x ≤ z → y ≤ z → x ⊔ y ≤ z
--
-- Por le_antisymm, basta demostrar las siguientes relaciones:
--    (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)                                      (1)
--    x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z                                      (2)
--
-- Para demostrar (1), por sup_le, basta probar
--    x ⊔ y ≤ x ⊔ (y ⊔ z)                                           (1a)
--    z ≤ x ⊔ (y ⊔ z)                                               (1b)
--
-- Para demostrar (1a), por sup_le, basta probar
--    x ≤ x ⊔ (y ⊔ z)                                              (1a1)
--    y ≤ x ⊔ (y ⊔ z)                                              (1a2)
--
-- La (1a1) se tiene por le_sup_left.
--
-- La (1a2) se tiene por la siguiente cadena de desigualdades:
--    y ≤ y ⊔ z          [por le_sup_left]
--      ≤ x ⊔ (y ⊔ z)    [por le_sup_right]
--
-- La (1b) se tiene por la siguiente cadena de desigualdades
--    z ≤ y ⊔ z          [por le_sup_right]
--      ≤ x ⊔ (y ⊔ z)    [por le_sup_right]
--
-- Para demostrar (2), por sup_le, basta probar
--    x ≤ (x ⊔ y) ⊔ z                                               (2a)
--    y ⊔ z ≤ (x ⊔ y) ⊔ z                                           (2b)
--
-- La (2a) se demuestra por la siguiente cadena de desigualdades:
--    x ≤ x ⊔ y          [por le_sup_left]
--      ≤ (x ⊔ y) ⊔ z    [por le_sup_left]
--
-- Para demostrar (2b), por sup_le, basta probar
--    y ≤ (x ⊔ y) ⊔ z                                              (2b1)
--    z ≤ (x ⊔ y) ⊔ z                                              (2b2)
--
-- La (2b1) se demuestra por la siguiente cadena de desigualdades:
--    y ≤ x ⊔ y          [por le_sup_right]
--      ≤ (x ⊔ y) ⊔ z    [por le_sup_left]
--
-- La (2b2) se tiene por le_sup_right.

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Order.Lattice

variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  have h1 : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z) := by
  { have h1a : x ⊔ y ≤ x ⊔ (y ⊔ z) := by
    { have h1a1 : x ≤ x ⊔ (y ⊔ z) := by exact le_sup_left
      have h1a2 : y ≤ x ⊔ (y ⊔ z) := calc
        y ≤ y ⊔ z       := by exact le_sup_left
        _ ≤ x ⊔ (y ⊔ z) := by exact le_sup_right
      show x ⊔ y ≤ x ⊔ (y ⊔ z)
      exact sup_le h1a1 h1a2 }
    have h1b : z ≤ x ⊔ (y ⊔ z) := calc
      z ≤ y ⊔ z       := by exact le_sup_right
      _ ≤ x ⊔ (y ⊔ z) := by exact le_sup_right
    show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    exact sup_le h1a h1b }
  have h2 : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z := by
  { have h2a : x ≤ (x ⊔ y) ⊔ z := calc
      x ≤ x ⊔ y       := by exact le_sup_left
      _ ≤ (x ⊔ y) ⊔ z := by exact le_sup_left
    have h2b : y ⊔ z ≤ (x ⊔ y) ⊔ z := by
    { have h2b1 : y ≤ (x ⊔ y) ⊔ z := calc
        y ≤ x ⊔ y       := by exact le_sup_right
        _ ≤ (x ⊔ y) ⊔ z := by exact le_sup_left
      have h2b2 : z ≤ (x ⊔ y) ⊔ z := by
        exact le_sup_right
      show  y ⊔ z ≤ (x ⊔ y) ⊔ z
      exact sup_le h2b1 h2b2 }
    show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    exact sup_le h2a h2b }
  show (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  · -- (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · -- x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      . -- x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      · -- y ≤ x ⊔ (y ⊔ z)
        apply le_trans
        . -- y ≤ y ⊔ z
          apply @le_sup_left _ _ y z
        . -- y ⊔ z ≤ x ⊔ (y ⊔ z)
          apply le_sup_right
    . -- z ≤ x ⊔ (y ⊔ z)
      apply le_trans
      . -- z ≤ x ⊔ (y ⊔ z)
        apply @le_sup_right _ _ y z
      . -- y ⊔ z ≤ x ⊔ (y ⊔ z)
        apply le_sup_right
  . -- x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    apply sup_le
    · -- x ≤ (x ⊔ y) ⊔ z
      apply le_trans
      . -- x ≤ x ⊔ y
        apply @le_sup_left _ _ x y
      . -- x ⊔ y ≤ (x ⊔ y) ⊔ z
        apply le_sup_left
    . -- y ⊔ z ≤ (x ⊔ y) ⊔ z
      apply sup_le
      · -- y ≤ (x ⊔ y) ⊔ z
        apply le_trans
        . -- y ≤ x ⊔ y
          apply @le_sup_right _ _ x y
        . -- x ⊔ y ≤ (x ⊔ y) ⊔ z
          apply le_sup_left
      . -- z ≤ (x ⊔ y) ⊔ z
        apply le_sup_right

-- 3ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      . apply le_sup_left
      · apply le_trans
        . apply @le_sup_left _ _ y z
        . apply le_sup_right
    . apply le_trans
      . apply @le_sup_right _ _ y z
      . apply le_sup_right
  . apply sup_le
    · apply le_trans
      . apply @le_sup_left _ _ x y
      . apply le_sup_left
    . apply sup_le
      · apply le_trans
        . apply @le_sup_right _ _ x y
        . apply le_sup_left
      . apply le_sup_right

-- 4ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  . -- (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    . -- x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le le_sup_left (le_sup_of_le_right le_sup_left)
    . -- z ≤ x ⊔ (y ⊔ z)
      apply le_sup_of_le_right le_sup_right
  . -- x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    apply sup_le
    . -- x ≤ (x ⊔ y) ⊔ z
      apply le_sup_of_le_left le_sup_left
    . -- y ⊔ z ≤ (x ⊔ y) ⊔ z
      apply sup_le (le_sup_of_le_left le_sup_right) le_sup_right

-- 5ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  . apply sup_le
    . apply sup_le le_sup_left (le_sup_of_le_right le_sup_left)
    . apply le_sup_of_le_right le_sup_right
  . apply sup_le
    . apply le_sup_of_le_left le_sup_left
    . apply sup_le (le_sup_of_le_left le_sup_right) le_sup_right

-- 6ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
    (le_sup_of_le_right le_sup_right))
  (sup_le
    (le_sup_of_le_left le_sup_left)
    (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))

-- 7ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
-- by apply?
sup_assoc x y z

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_of_le_left : z ≤ x → z ≤ x ⊔ y)
-- #check (le_sup_of_le_right : z ≤ y → z ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (sup_assoc x y z : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z))
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
