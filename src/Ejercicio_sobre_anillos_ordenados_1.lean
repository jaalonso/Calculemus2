-- Ejercicio_sobre_anillos_ordenados_1.lean
-- En los anillos ordenados, a ≤ b → 0 ≤ b - a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los anillos ordenados se verifica que
--    a ≤ b → 0 ≤ b - a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    sub_self         : a - a = 0
--    sub_le_sub_right : a ≤ b → ∀ (c : R), a - c ≤ b - c
--
-- Supongamos que
--    a ≤ b                                                          (1)
-- La demostración se tiene por la siguiente cadena de desigualdades:
--    0 = a - a    [por sub_self]
--      ≤ b - a    [por (1) y sub_le_sub_right]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
example : a ≤ b → 0 ≤ b - a :=
by
  intro h
  calc
    0 = a - a := (sub_self a).symm
    _ ≤ b - a := sub_le_sub_right h a

-- 2ª demostración
example : a ≤ b → 0 ≤ b - a :=
sub_nonneg.mpr

-- 3ª demostración
example : a ≤ b → 0 ≤ b - a :=
by simp

-- Lemas usados
-- ============

-- #check (sub_le_sub_right : a ≤ b → ∀ (c : R), a - c ≤ b - c)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
-- #check (sub_self a : a - a = 0)
