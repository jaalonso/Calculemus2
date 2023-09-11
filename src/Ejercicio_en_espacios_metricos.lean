-- Ejercicio_en_espacios_metricos.lean
-- En los espacios métricos, dist(x,y) ≥ 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los espacios métricos
--    0 ≤ dist x y
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas:
--    dist_comm x y             : dist x y = dist y x
--    dist_self x               : dist x x = 0
--    dist_triangle x y z       : dist x z ≤ dist x y + dist y z
--    mul_two a                 : a * 2 = a + a
--    nonneg_of_mul_nonneg_left : 0 ≤ a * b → 0 < b → 0 ≤ a
--    zero_lt_two               : 0 < 2
--
-- Por nonneg_of_mul_nonneg_left es suficiente demostrar las siguientes
-- desigualdades:
--    0 ≤ dist x y * 2                                               (1)
--    0 < 2                                                          (2)
--
-- La (1) se demuestra por las siguiente cadena de desigualdades:
--    0 = dist x x               [por dist_self]
--      ≤ dist x y + dist y x    [por dist_triangle]
--      = dist x y + dist x y    [por dist_comm]
--      = dist x y * 2           [por mul_two]
--
-- La (2) se tiene por zero_lt_two.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Topology.MetricSpace.Basic
variable {X : Type _} [MetricSpace X]
variable (x y : X)

-- 1ª demostración
example : 0 ≤ dist x y :=
by
  have h1 : 0 ≤ dist x y * 2 := calc
    0 = dist x x            := (dist_self x).symm
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm x y]
    _ = dist x y * 2        := (mul_two (dist x y)).symm
  show 0 ≤ dist x y
  exact nonneg_of_mul_nonneg_left h1 zero_lt_two

-- 2ª demostración
example : 0 ≤ dist x y :=
by
  apply nonneg_of_mul_nonneg_left
  . -- 0 ≤ dist x y * 2
    calc 0 = dist x x            := by simp only [dist_self]
         _ ≤ dist x y + dist y x := by simp only [dist_triangle]
         _ = dist x y + dist x y := by simp only [dist_comm]
         _ = dist x y * 2        := by simp only [mul_two]
  . -- 0 < 2
    exact zero_lt_two

-- 3ª demostración
example : 0 ≤ dist x y :=
by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- 3ª demostración
example : 0 ≤ dist x y :=
-- by apply?
dist_nonneg

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- variable (z : X)
-- #check (dist_comm x y : dist x y = dist y x)
-- #check (dist_nonneg : 0 ≤ dist x y)
-- #check (dist_self x : dist x x = 0)
-- #check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- #check (mul_two a : a * 2 = a + a)
-- #check (nonneg_of_mul_nonneg_left : 0 ≤ a * b → 0 < b → 0 ≤ a)
-- #check (zero_lt_two : 0 < 2)
