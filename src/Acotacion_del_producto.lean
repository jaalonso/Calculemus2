-- Acotacion_del_producto.lean
-- En ℝ, {0 < ε, ε ≤ 1, |x| < ε, |y| < ε} ⊢ |xy| < ε
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para todos los números reales x, y, ε si
--    0 < ε
--    ε ≤ 1
--    |x| < ε
--    |y| < ε
-- entonces
--    |x * y| < ε
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    abs_mul          : |a * b| = |a| * |b|
--    zero_mul         : 0 * a = 0
--    abs_nonneg a     : 0 ≤ |a|
--    lt_of_le_of_ne   : a ≤ b → a ≠ b → a < b
--    ne_comm          : a ≠ b ↔ b ≠ a
--    mul_lt_mul_left  : 0 < a → (a * b < a * c ↔ b < c)
--    mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c)
--    mul_le_mul_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c)
--    one_mul          : 1 * a = a
--
-- Sean x y ε ∈ ℝ tales que
--    0 < ε                                                         (he1)
--    ε ≤ 1                                                         (he2)
--    |x| < ε                                                       (hx)
--    |y| < ε                                                       (hy)
-- y tenemos que demostrar que
--    |x * y| < ε
-- Lo haremos distinguiendo caso según |x| = 0.
--
-- 1º caso. Supongamos que
--    |x| = 0                                                        (1)
-- Entonces,
--    |x * y| = |x| * |y|    [por abs_mul]
--            = 0 * |y|      [por h1]
--            = 0            [por zero_mul]
--            < ε            [por he1]
--
-- 2º caso. Supongamos que
--    |x| ≠ 0                                                        (2)
-- Entonces, por lt_of_le_of_ne, abs_nonneg y ne_comm, se tiene
--    0 < x                                                          (3)
-- y, por tanto,
--    |x * y| = |x| * |y|    [por abs_mul]
--            < |x| * ε      [por mul_lt_mul_left, (3) y (hy)]
--            < ε * ε        [por mul_lt_mul_right, (he1) y (hx)]
--            ≤ 1 * ε        [por mul_le_mul_right, (he1) y (he2)]
--            = ε            [por one_mul]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases h : (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc
      |x * y|
         = |x| * |y| := abs_mul x y
      _  = 0 * |y|   := by rw [h]
      _  = 0         := zero_mul (abs y)
      _  < ε         := he1
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := abs_nonneg x
      show 0 < |x|
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc |x * y|
         = |x| * |y| := abs_mul x y
       _ < |x| * ε   := (mul_lt_mul_left h1).mpr hy
       _ < ε * ε     := (mul_lt_mul_right he1).mpr hx
       _ ≤ 1 * ε     := (mul_le_mul_right he1).mpr he2
       _ = ε         := one_mul ε

-- 2ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases h : (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by apply abs_mul
            _ = 0 * |y|   := by rw [h]
            _ = 0         := by apply zero_mul
            _ < ε         := by apply he1
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := by apply abs_nonneg
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by rw [abs_mul]
            _ < |x| * ε   := by apply (mul_lt_mul_left h1).mpr hy
            _ < ε * ε     := by apply (mul_lt_mul_right he1).mpr hx
            _ ≤ 1 * ε     := by apply (mul_le_mul_right he1).mpr he2
            _ = ε         := by rw [one_mul]

-- 3ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases h : (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc |x * y| = |x| * |y| := by simp only [abs_mul]
               _ = 0 * |y|   := by simp only [h]
               _ = 0         := by simp only [zero_mul]
               _ < ε         := by simp only [he1]
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := by simp only [abs_nonneg]
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by simp [abs_mul]
            _ < |x| * ε   := by simp only [mul_lt_mul_left, h1, hy]
            _ < ε * ε     := by simp only [mul_lt_mul_right, he1, hx]
            _ ≤ 1 * ε     := by simp only [mul_le_mul_right, he1, he2]
            _ = ε         := by simp only [one_mul]

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (lt_of_le_of_ne : a ≤ b → a ≠ b → a < b)
-- #check (mul_le_mul_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c))
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c))
-- #check (ne_comm : a ≠ b ↔ b ≠ a)
-- #check (one_mul a : 1 * a = a)
-- #check (zero_mul a : 0 * a = 0)
