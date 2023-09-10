-- Ejercicio_sobre_anillos_ordenados_2.lean
-- En los anillos ordenados, 0 ≤ b - a → a ≤ b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los anillos ordenados
--    0 ≤ b - a → a ≤ b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    zero_add a : 0 + a = a
--    add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a
--    sub_add_cancel a b : a - b + b = -a
-- Supongamos que
--    0 ≤ b - a                                                      (1)
-- La demostración se tiene por la siguiente cadena de desigualdades:
--    a = 0 + a          [por zero_add]
--      ≤ (b - a) + a    [por (1) y add_le_add_right]
--      = b              [por sub_add_cancel]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by
  intro h
  calc
    a = 0 + a       := (zero_add a).symm
    _ ≤ (b - a) + a := add_le_add_right h a
    _ = b           := sub_add_cancel b a

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by apply?
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by simp

-- Lemas usados
-- ============

-- #check (zero_add a : 0 + a = a)
-- #check (add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a)
-- #check (sub_add_cancel a b : a - b + b = a)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
