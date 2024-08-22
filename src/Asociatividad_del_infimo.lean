-- Asociatividad_del_infimo.lean
-- En los retículos, (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los retículos se verifica que
--     (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración se usarán los siguientes lemas
--    le_antisymm : x ≤ y → y ≤ x → x = y
--    le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y
--    inf_le_left : x ⊓ y ≤ x
--    inf_le_right : x ⊓ y ≤ y)
--
-- Por le_antisym, es suficiente demostrar las siguientes relaciones:
--    (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)                                      (1)
--    x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z                                      (2)
--
-- Para demostrar (1), por le_inf, basta probar que
--    (x ⊓ y) ⊓ z ≤ x                                               (1a)
--    (x ⊓ y) ⊓ z ≤ y ⊓ z                                           (1b)
--
-- La (1a) se demuestra por la siguiente cadena de desigualdades
--    (x ⊓ y) ⊓ z ≤ x ⊓ y   [por inf_le_left]
--                ≤ x       [por inf_le_left]
--
-- Para demostrar (1b), por le_inf, basta probar que
--    (x ⊓ y) ⊓ z ≤ y                                              (1b1)
--    (x ⊓ y) ⊓ z ≤ z                                              (1b2)
--
-- La (1b1) se demuestra por la siguiente cadena de desigualdades
--    (x ⊓ y) ⊓ z ≤ x ⊓ y   [por inf_le_left]
--                ≤ y       [por inf_le_right]
--
-- La (1b2) se tiene por inf_le_right.
--
-- Para demostrar (2), por le_inf, basta probar que
--    x ⊓ (y ⊓ z) ≤ x ⊓ y                                           (2a)
--    x ⊓ (y ⊓ z) ≤ z                                               (2b)
--
-- Para demostrar (2a), por le_inf, basta probar que
--    x ⊓ (y ⊓ z) ≤ x                                              (2a1)
--    x ⊓ (y ⊓ z) ≤ y                                              (2a2)
--
-- La (2a1) se tiene por inf_le_left.
--
-- La (2a2) se demuestra por la siguiente cadena de desigualdades
--    x ⊓ (y ⊓ z) ≤ y ⊓ z   [por inf_le_right]
--                ≤ y       [por inf_le_left]
--
-- La (2b) se demuestra por la siguiente cadena de desigualdades
--    x ⊓ (y ⊓ z) ≤ y ⊓ z   [por inf_le_right]
--                ≤ z       [por inf_le_right]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  have h1 : (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z) := by
  { have h1a : (x ⊓ y) ⊓ z ≤ x := calc
      (x ⊓ y) ⊓ z ≤ x ⊓ y := by exact inf_le_left
                _ ≤ x     := by exact inf_le_left
    have h1b : (x ⊓ y) ⊓ z ≤ y ⊓ z := by
    { have h1b1 : (x ⊓ y) ⊓ z ≤ y := calc
        (x ⊓ y) ⊓ z ≤ x ⊓ y := by exact inf_le_left
                  _ ≤ y     := by exact inf_le_right
      have h1b2 : (x ⊓ y) ⊓ z ≤ z :=
        inf_le_right
      show (x ⊓ y) ⊓ z ≤ y ⊓ z
      exact le_inf h1b1 h1b2 }
    show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    exact le_inf h1a h1b }
  have h2 : x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z := by
  { have h2a : x ⊓ (y ⊓ z) ≤ x ⊓ y := by
    { have h2a1 : x ⊓ (y ⊓ z) ≤ x :=
        inf_le_left
      have h2a2 : x ⊓ (y ⊓ z) ≤ y := calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z := by exact inf_le_right
                  _ ≤ y     := by exact inf_le_left
      show x ⊓ (y ⊓ z) ≤ x ⊓ y
      exact le_inf h2a1 h2a2 }
    have h2b : x ⊓ (y ⊓ z) ≤ z := by calc
      x ⊓ (y ⊓ z) ≤ y ⊓ z := by exact inf_le_right
                _ ≤ z     := by exact inf_le_right
    show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    exact le_inf h2a h2b }
  show (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    . apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_right
      . apply inf_le_right
  . apply le_inf
    · apply le_inf
      · apply inf_le_left
      . apply le_trans
        apply inf_le_right
        apply inf_le_left
    . apply le_trans
      apply inf_le_right
      apply inf_le_right

-- 3ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  apply le_antisymm
  . apply le_inf
    . apply inf_le_of_left_le inf_le_left
    . apply le_inf (inf_le_of_left_le inf_le_right) inf_le_right
  . apply le_inf
    . apply le_inf inf_le_left (inf_le_of_right_le inf_le_left)
    . apply inf_le_of_right_le inf_le_right

-- 4ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
le_antisymm
  (le_inf
    (inf_le_of_left_le inf_le_left)
    (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
    (inf_le_of_right_le inf_le_right))

-- 5ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by apply?
inf_assoc x y z

-- Lemas usados
-- ============

-- #check (inf_assoc x y z : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z))
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_of_left_le : x ≤ z → x ⊓ y ≤ z)
-- #check (inf_le_of_right_le : y ≤ z → x ⊓ y ≤ z)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
