-- Divisibilidad_de_producto.lean
-- Si x,y,z ∈ ℕ, entonces x ∣ yxz
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si x, y, z ∈ ℕ, entonces
--    x ∣ y * x * z
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la transitividad de la divisibilidad aplicada a las relaciones
--    x ∣ yx
--    yx ∣ yxz

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (x y z : ℕ)

-- 1ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  have h1 : x ∣ y * x :=
    dvd_mul_left x y
  have h2 : (y * x) ∣ (y * x * z) :=
    dvd_mul_right (y * x) z
  show x ∣ y * x * z
  exact dvd_trans h1 h2

-- 2ª demostración
-- ===============

example : x ∣ y * x * z :=
dvd_trans (dvd_mul_left x y) (dvd_mul_right (y * x) z)

-- 3ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

-- Lemas usados
-- ============

-- #check (dvd_mul_left x y : x ∣ y * x)
-- #check (dvd_mul_right x y : x ∣ x * y)
-- #check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
