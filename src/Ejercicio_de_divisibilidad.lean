-- Ejercicio_de_divisibilidad.lean
-- Si x divide a w, también divide a y(xz)+x²+w²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    x ∣ w
-- entonces
--    x ∣ y * (x * z) + x^2 + w^2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la divisibilidad de la suma basta probar que
--    x | yxz                                                         (1)
--    x | x²                                                          (2)
--    x | w²                                                          (3)
--
-- Para demostrar (1), por la divisibilidad del producto se tiene
--    x | xz
-- y, de nuevo por la divisibilidad del producto,
--    x | y(xz).
--
-- La propiedad (2) se tiene por la definición de cuadrado y la
-- divisibilidad del producto.
--
-- La propiedad (3) se tiene por la definición de cuadrado, la hipótesis
-- y la divisibilidad del producto.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (w x y z : ℕ)

-- 1ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  have h1 : x ∣ x * z :=
    dvd_mul_right x z
  have h2 : x ∣ y * (x * z) :=
    dvd_mul_of_dvd_right h1 y
  have h3 : x ∣ x^2 := by
    apply dvd_mul_left
  have h4 : x ∣ w * w :=
    dvd_mul_of_dvd_left h w
  have h5 : x ∣ w^2 := by
    rwa [← pow_two w] at h4
  have h6 : x ∣ y * (x * z) + x^2 :=
    dvd_add h2 h3
  show x ∣ y * (x * z) + x^2 + w^2
  exact dvd_add h6 h5

-- 2ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  apply dvd_add
  { apply dvd_add
    { apply dvd_mul_of_dvd_right
      apply dvd_mul_right }
    { rw [pow_two]
      apply dvd_mul_right }}
  { rw [pow_two]
    apply dvd_mul_of_dvd_left h }

-- 3ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  repeat' apply dvd_add
  { apply dvd_mul_of_dvd_right
    apply dvd_mul_right }
  { rw [pow_two]
    apply dvd_mul_right }
  { rw [pow_two]
    apply dvd_mul_of_dvd_left h }

-- Lemas usados
-- ============

-- #check (dvd_add : x ∣ y → x ∣ z → x ∣ y + z)
-- #check (dvd_mul_left x y : x ∣ y * x)
-- #check (dvd_mul_right x y : x ∣ x * y)
-- #check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
-- #check (dvd_mul_of_dvd_right : x ∣ y → ∀ (c : ℕ), x ∣ c * y)
-- #check (pow_two x : x ^ 2 = x * x)
