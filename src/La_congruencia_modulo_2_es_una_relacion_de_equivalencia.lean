-- La_congruencia_modulo_2_es_una_relacion_de_equivalencia.lean
-- La congruencia módulo 2 es una relación de equivalencia
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Se define la relación R entre los números enteros de forma que x está
-- relacionado con y si x-y es divisible por 2. Demostrar que R es una
-- relación de equivalencia.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que R es reflexiva, simétrica y transitiva.
--
-- Para demostrar que R es reflexiva, sea x ∈ ℤ. Entonces, x - x = 0 que
-- es divisible por 2. Luego, xRx.
--
-- Para demostrar que R es simétrica, sean x, y ∈ ℤ tales que
-- xRy. Entonces, x - y es divisible por 2. Luego, existe un a ∈ ℤ tal
-- que
--    x - y = 2·a
-- Por tanto,
--    y - x = 2·(-a)
-- Por lo que y - x es divisible por 2 y yRx.
--
-- Para demostrar que R es transitiva, sean x, y, z ∈ ℤ tales que xRy y
-- yRz. Entonces, tanto x - y como y - z son divibles por 2. Luego,
-- existen a, b ∈ ℤ tales que
--    x - y = 2·a
--    y - z = 2·b
-- Por tanto,
--    x - z = 2·(a + b)
-- Por lo que x - z es divisible por 2 y xRz.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

def R (m n : ℤ) := 2 ∣ (m - n)

-- 1ª demostración
-- ===============

example : Equivalence R :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : ℤ), R x x
    intro x
    -- x : ℤ
    -- ⊢ R x x
    unfold R
    -- ⊢ 2 ∣ x - x
    rw [sub_self]
    -- ⊢ 2 ∣ 0
    exact dvd_zero 2
  . -- ⊢ ∀ {x y : ℤ}, R x y → R y x
    intros x y hxy
    -- x y : ℤ
    -- hxy : R x y
    -- ⊢ R y x
    unfold R at *
    -- hxy : 2 ∣ x - y
    -- ⊢ 2 ∣ y - x
    cases' hxy with a ha
    -- a : ℤ
    -- ha : x - y = 2 * a
    use -a
    -- ⊢ y - x = 2 * -a
    calc y - x
         = -(x - y) := (neg_sub x y).symm
       _ = -(2 * a) := by rw [ha]
       _ = 2 * -a   := neg_mul_eq_mul_neg 2 a
  . -- ⊢ ∀ {x y z : ℤ}, R x y → R y z → R x z
    intros x y z hxy hyz
    -- x y z : ℤ
    -- hxy : R x y
    -- hyz : R y z
    -- ⊢ R x z
    cases' hxy with a ha
    -- a : ℤ
    -- ha : x - y = 2 * a
    cases' hyz with b hb
    -- b : ℤ
    -- hb : y - z = 2 * b
    use a + b
    -- ⊢ x - z = 2 * (a + b)
    calc x - z
         = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
       _ = 2 * a + 2 * b     := congrArg₂ (. + .) ha hb
       _ = 2 * (a + b)       := (mul_add 2 a b).symm

-- 2ª demostración
-- ===============

example : Equivalence R :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : ℤ), R x x
    intro x
    -- x : ℤ
    -- ⊢ R x x
    simp [R]
  . -- ⊢ ∀ {x y : ℤ}, R x y → R y x
    rintro x y ⟨a, ha⟩
    -- x y a : ℤ
    -- ha : x - y = 2 * a
    -- ⊢ R y x
    use -a
    -- ⊢ y - x = 2 * -a
    linarith
  . -- ⊢ ∀ {x y z : ℤ}, R x y → R y z → R x z
    rintro x y z ⟨a, ha⟩ ⟨b, hb⟩
    -- x y z a : ℤ
    -- ha : x - y = 2 * a
    -- b : ℤ
    -- hb : y - z = 2 * b
    -- ⊢ R x z
    use a + b
    -- ⊢ x - z = 2 * (a + b)
    linarith

-- Lemas usados
-- ============

-- variable (a b c x y x' y' : ℤ)
-- #check (congrArg₂  (. + .) : x = x' → y = y' → x + y = x' + y')
-- #check (dvd_zero a : a ∣ 0)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (neg_mul_eq_mul_neg a b : -(a * b) = a * -b)
-- #check (neg_sub a b : -(a - b) = b - a)
-- #check (sub_add_sub_cancel a b c : a - b + (b - c) = a - c)
-- #check (sub_self a : a - a = 0)
