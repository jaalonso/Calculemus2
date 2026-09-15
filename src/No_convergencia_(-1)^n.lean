-- Reto_2.lean
-- Soluciones de 2º reto (17 de mayo de 2026).
-- La sucesión 1, -1, 1, -1,... no esconvergente.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En el reto de esta semana continuamos explorando la convergencia de
-- sucesiones, retomando el trabajo de la semana anterior. El problema
-- consiste en demostrar que la sucesión definida por 1, -1, 1, -1,,,,
-- no converge. Para ello, se propone completar la siguiente
-- demostración en Lean 4:
--    import Mathlib.Data.Real.Basic
--    import Mathlib.Tactic
--
--    variable {a : ℕ → ℝ}
--
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    def SucConv (a : ℕ → ℝ) : Prop :=
--      ∃ L, LimSuc a L
--
--    example
--      (ha : ∀ n, a n = (-1) ^ n)
--      : ¬ SucConv a :=
--    by sorry
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a la sucesión definida por a(n) = (-1)^n. Supongamos que a es
-- convergente. Entonces, existe un L tal que a converge L. Por tanto,
-- existe un k ∈ ℕ tal que,
--    ∀n ≥ k, |a(n) - L| < 1/2                                      (1)
-- Entonces,
--    2 = |2|
--      = |(1 - L) + (1 + L)|
--      = |(1 - L) + (-1)(-1 - L)|
--      ≤ |1 - L| + |(-1)(-1 - L)|
--      = |1 - L| + |-1 - L|
--      = |(-1)^{2k} - L| + |(-1)^{2k+1} - L|
--      = |a(2k) - L| + |a(2k+1) - L|
--      < 1/2 + 1/2                            [por (1), 2k ≥ k y 2k+1 ≥ k]
--      = 1
-- Luego, 2 < 1 que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a : ℕ → ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def SucConv (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

-- 1ª demostración
-- ===============

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro h
  -- h : SucConv a
  -- ⊢ False
  obtain ⟨L, hL⟩ := h
  -- L : ℝ
  -- hL : LimSuc a L
  obtain ⟨k, hk⟩ := hL (1/2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1 / 2
  have h1 : ¬(2 : ℝ) < 1 := lt_asymm one_lt_two
  apply h1
  -- ⊢ 2 < 1
  calc
    2 = |2|                                        := by grind
    _ = |(1 - L) + (1 + L)|                        := by grind
    _ = |(1 - L) + (-1)*(-1 - L)|                  := by grind
    _ ≤ |1 - L| + |(-1)*(-1 - L)|                  := by grind
    _ = |1 - L| + |-1 - L|                         := by grind
    _ = |(-1:ℝ)^(2*k) - L| + |(-1:ℝ)^(2*k+1) - L|  := by
          have h2 : (-1:ℝ)^(2*k) = 1    := by simp
          have h3 : (-1:ℝ)^(2*k+1) = -1 := by grind
          rw [h2, h3]
    _ = |a (2*k) - L| + |a (2*k+1) - L|            := by simp [*]
    _ < 1/2 + 1/2                                  := by grind
    _ = 1                                          := by grind

-- 2ª solución
-- ===========

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬SucConv a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  obtain ⟨k, hk⟩ := hL (1 / 2) (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1 / 2
  have h1 := hk (2 * k) (by omega)
  -- h1 : |a (2 * k) - L| < 1 / 2
  have h2 := hk (2 * k + 1) (by omega)
  -- h2 : |a (2 * k + 1) - L| < 1 / 2
  simp only [ha, pow_succ] at h1 h2
  -- h1 : |(-1) ^ (2 * k) - L| < 1 / 2
  -- h2 : |(-1) ^ (2 * k) * -1 - L| < 1 / 2
  norm_num at h1 h2
  -- h1 : |1 - L| < 1 / 2
  -- h2 : |-1 - L| < 1 / 2
  rw [abs_lt] at h1 h2
  -- h1 : -(1 / 2) < 1 - L ∧ 1 - L < 1 / 2
  -- h2 : -(1 / 2) < -1 - L ∧ -1 - L < 1 / 2
  linarith

-- 3ª demostración
-- ===============

variable {x y z x' y' : ℝ}
variable {m n k : ℕ}
variable (f : ℝ → ℝ)

lemma L1 : (1 - x) + (1 + x) = 2 := by
  calc (1 - x) + (1 + x)
       = 1 + 1             := sub_add_add_cancel 1 1 x
     _ = 2                 := one_add_one_eq_two

lemma L2 : (-1:ℝ) * -1 = 1 := by
  calc (-1:ℝ) * -1
       = 1 * 1   := neg_mul_neg 1 1
     _ = 1       := one_mul 1

lemma L3 : -1 * -x = x := by
  calc -1 * -x
       = -(1 * -x) := neg_mul 1 (-x)
     _ = - -x      := congr_arg (- ·) (one_mul (-x))
     _ = x         := neg_neg x

lemma L4 : -1 * (-1 - x) = 1 + x := by
  calc -1 * (-1 - x)
       = -1 * (-1 + -x)     := congr_arg (-1 * ·) (sub_eq_add_neg (-1) x)
     _ = -1 * -1 + -1 * -x  := left_distrib (-1) (-1) (-x)
     _ = 1 + -1 * -x        := congr_arg (· + (-1)*(-x)) L2
     _ = 1 + x              := congr_arg ( 1 + ·) L3

lemma L5 : |-1 * (-1 - x)| = |-1 - x| := by
  calc |-1 * (-1 - x)|
       = |-1| * |-1 - x| := abs_mul (-1) (-1 - x)
     _ = |1| * |-1 - x|  := congrArg (· * |-1 - x|) (abs_neg 1)
     _ = 1 * |-1 - x|    := congrArg (· * |-1 - x|) abs_one
     _ = |-1 - x|        := one_mul |-1 - x|

lemma L6 : (-1:ℝ)^(2*n) = 1 := by
  calc (-1:ℝ)^(2*n)
       = ((-1:ℝ)^2)^n := pow_mul (-1) 2 n
     _ = (1:ℝ)^n      := congr_arg ( · ^ n) neg_one_sq
     _ = 1            := one_pow n

lemma L7 : (-1:ℝ)^(2*n+1) = -1 := by
  calc (-1:ℝ)^(2*n+1)
       = (-1)^(2*n) * -1 := pow_succ (-1) (2 * n)
     _ = 1 * -1          := congr_arg (· * -1) L6
     _ = -1              := one_mul (-1)

lemma L8 : n ≤ 2 * n := by
  calc n
       = 1 * n := (one_mul n).symm
     _ ≤ 2 * n := Nat.mul_le_mul_right n one_le_two

lemma L9
  (hk : ∀ n ≥ k, |a n - x| < 1 / 2)
  : |a (2*k) - x| < 1 / 2 :=
hk (2*k) L8

lemma L10 : n ≤ 2 * n + 1 := by
  calc n
       ≤ 2 * n     := L8
     _ ≤ 2 * n + 1 := Nat.le_add_right (2 * n) 1

lemma L11
  (hk : ∀ n ≥ k, |a n - x| < 1 / 2)
  : |a (2*k+1) - x| < 1 / 2 :=
hk (2*k+1) L10

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro h
  -- h : SucConv a
  -- ⊢ False
  obtain ⟨L, hL⟩ := h
  -- L : ℝ
  -- hL : LimSuc a L
  obtain ⟨k, hk⟩ := hL (1/2) one_half_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1 / 2
  have h1 : ¬(2 : ℝ) < 1 := lt_asymm one_lt_two
  apply h1
  -- ⊢ 2 < 1
  calc
    2 = |2| :=
          abs_two.symm
    _ = |(1 - L) + (1 + L)| :=
          congrArg abs L1.symm
    _ = |(1 - L) + (-1)*(-1 - L)| :=
          congr_arg (abs ((1 - L) + ·)) L4.symm
    _ ≤ |1 - L| + |(-1)*(-1 - L)| :=
          abs_add_le (1 - L) (-1 * (-1 - L))
    _ = |1 - L| + |-1 - L| :=
          congr_arg (|1 - L| + ·) L5
    _ = |(-1:ℝ)^(2*k) - L| + |(-1:ℝ)^(2*k+1) - L|  :=
          congrArg₂ (|· - L| + |· - L|) L6.symm L7.symm
    _ = |a (2*k) - L| + |a (2*k+1) - L| :=
          congrArg₂ (· + ·)
            (congrArg (|· - L|) (ha (2*k)).symm)
            (congrArg (|· - L|) (ha (2*k+1)).symm)
    _ < 1 / 2 + 1 / 2 :=
          add_lt_add (L9 hk) (L11 hk)
    _ = 1 := add_halves 1

-- Lemas usados
-- ============

variable (a b c d : ℝ)
#check (Nat.le_add_right n k : n ≤ n + k)
#check (Nat.mul_le_mul_right k : n ≤ m → n * k ≤ m * k)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_neg a : |(-a)| = |a|)
#check (abs_one : |(1 : ℝ)| = 1)
#check (abs_two : |(2 : ℝ)| = 2)
#check (add_halves a : a / 2 + a / 2 = a)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (left_distrib a b c : a * (b + c) = a * b + a * c)
#check (lt_asymm  : a < b → ¬b < a)
#check (neg_mul a b : -a * b = -(a * b))
#check (neg_mul_neg a b : -a * -b = a * b)
#check (neg_neg a : - -a = a)
#check (neg_one_sq : (-1) ^ 2 = 1)
#check (one_add_one_eq_two : 1 + 1 = 2)
#check (one_half_pos : (0 : ℝ) < 1 / 2)
#check (one_lt_two : 1 < 2)
#check (one_mul a : 1 * a = a)
#check (one_pow n : 1 ^ n = 1)
#check (pow_mul a m n : a ^ (m * n) = (a ^ m) ^ n)
#check (pow_succ a n : a ^ (n + 1) = a ^ n * a)
#check (sub_add_add_cancel a b c : a - c + (b + c) = a + b)
#check (sub_eq_add_neg a b : a - b = a + -b)
