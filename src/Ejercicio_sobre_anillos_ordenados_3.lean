-- Ejercicio_sobre_anillos_ordenados_3.lean
-- En los anillos ordenados, {a ≤ b, 0 ≤ c} ⊢ ac ≤ bc
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, en los anillos ordenados, si
--    a ≤ b
--    0 ≤ c
-- entonces
--    a * c ≤ b * c
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    sub_nonneg                 : 0 ≤ a - b ↔ b ≤ a)
--    mul_nonneg                 : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
--    sub_mul a b c              : (a - b) * c = a * c - b * c)
--
-- Supongamos que
--    a ≤ b                                                          (1)
--    0 ≤ c
-- De (1), por sub_nonneg, se tiene
--    0 ≤ b - a
-- y con (2), por mul_nonneg, se tiene
--    0 ≤ (b - a) * c
-- que, por sub_mul, da
--    0 ≤ b * c - a * c
-- y, aplicándole sub_nonneg, se tiene
--    a * c ≤ b * c

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a :=
    sub_nonneg.mpr h1
  have h4 : 0 ≤ b * c - a * c := calc
    0 ≤ (b - a) * c   := mul_nonneg h3 h2
    _ = b * c - a * c := sub_mul b a c
  show a * c ≤ b * c
  exact sub_nonneg.mp h4

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a := sub_nonneg.mpr h1
  have h4 : 0 ≤ (b - a) * c := mul_nonneg h3 h2
  -- h4 : 0 ≤ b * c - a * c
  rw [sub_mul] at h4
  -- a * c ≤ b * c
  exact sub_nonneg.mp h4

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  -- 0 ≤ b * c - a * c
  apply sub_nonneg.mp
  -- 0 ≤ (b - a) * c
  rw [← sub_mul]
  apply mul_nonneg
  . -- 0 ≤ b - a
    exact sub_nonneg.mpr h1
  . -- 0 ≤ c
    exact h2

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  apply sub_nonneg.mp
  rw [← sub_mul]
  apply mul_nonneg (sub_nonneg.mpr h1) h2

-- 5ª demostración
example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
-- by apply?
mul_le_mul_of_nonneg_right h1 h2

-- Lemas usados
-- ============

-- #check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
-- #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- #check (sub_mul a b c : (a - b) * c = a * c - b * c)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
