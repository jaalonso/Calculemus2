-- No_convergencia_(-1)^n.lean
-- La sucesión 1, -1, 1, -1, ... no es convergente.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-abril-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la sucesión 1, -1, 1, -1, ... no es convergente.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a la sucesión definida por a(n) = (-1)^n. Supongamos que a es
-- convergente. Entonces, existe un L tal que a converge L. Por tanto,
-- existe un N ∈ ℕ tal que,
--    ∀n ≥ N, |a(n) - L| < 1/2                                      (1)
-- Entonces,
--    2 = |2|
--      = |(1 - L) + (1 + L)|
--      = |(1 - L) + (-1)(-1 - L)|
--      ≤ |1 - L| + |(-1)(-1 - L)|
--      = |1 - L| + |-1 - L|
--      = |(-1)^{2N} - L| + |(-1)^{2N+1} - L|
--      = |a(2N) - L| + |a(2N+1) - L|
--      < 1/2 + 1/2                            [por (1), 2N ≥ N y 2N+1 ≥ N]
--      = 1
-- Luego, 2 < 1 que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a : ℕ → ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

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
  choose L hL using h
  -- L : ℝ
  -- hL : LimSuc a L
  choose N hN using hL (1/2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1 / 2
  have h1 : (2:ℝ) < 1 := calc
    2 = |2|                                        := by grind
    _ = |(1 - L) + (1 + L)|                        := by grind
    _ = |(1 - L) + (-1)*(-1 - L)|                  := by grind
    _ ≤ |1 - L| + |(-1)*(-1 - L)|                  := by grind
    _ = |1 - L| + |-1 - L|                         := by grind
    _ = |(-1:ℝ)^(2*N) - L| + |(-1:ℝ)^(2*N+1) - L|  := by
          have h2 : (-1:ℝ)^(2*N) = 1    := by simp
          have h3 : (-1:ℝ)^(2*N+1) = -1 := by grind
          rw [h2, h3]
    _ = |a (2*N) - L| + |a (2*N+1) - L|            := by simp [*]
    _ < 1/2 + 1/2                                  := by grind
    _ = 1                                          := by grind
  linarith

-- 2ª demostración
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
  (hN : ∀ n ≥ N, |a n - x| < 1 / 2)
  : |a (2*N) - x| < 1 / 2 :=
hN (2*N) L8

lemma L10 : n ≤ 2 * n + 1 := by
  calc n
       ≤ 2 * n     := L8
     _ ≤ 2 * n + 1 := Nat.le_add_right (2 * n) 1

lemma L11
  (hN : ∀ n ≥ N, |a n - x| < 1 / 2)
  : |a (2*N+1) - x| < 1 / 2 :=
hN (2*N+1) L10

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro h
  -- h : SucConv a
  -- ⊢ False
  choose L hL using h
  -- L : ℝ
  -- hL : LimSuc a L
  choose N hN using hL (1/2) one_half_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1 / 2
  have h1 : (2:ℝ) < 1 := by calc
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
    _ = |(-1:ℝ)^(2*N) - L| + |(-1:ℝ)^(2*N+1) - L|  :=
          congrArg₂ (|· - L| + |· - L|) L6.symm L7.symm
    _ = |a (2*N) - L| + |a (2*N+1) - L| :=
          congrArg₂ (· + ·)
            (congrArg (|· - L|) (ha (2*N)).symm)
            (congrArg (|· - L|) (ha (2*N+1)).symm)
    _ < 1 / 2 + 1 / 2 :=
          add_lt_add (L9 hN) (L11 hN)
    _ = 1 := add_halves 1
  have h2 : (1:ℝ) < 1 := lt_trans one_lt_two h1
  exact (lt_irrefl 1) h2

-- Lemas usados
-- ============

#check (Nat.le_add_right n m : n ≤ n + m)
#check (Nat.mul_le_mul_right k : n ≤ m → n * k ≤ m * k)
#check (abs_add_le x y : |x + y| ≤ |x| + |y|)
#check (add_halves x : x / 2 + x / 2 = x)
#check (add_lt_add : x < x' → y < y' → x + y < x' + y')
#check (congrArg₂  (· + ·) : x = x' → y = y' → x + y = x' + y')
#check (congr_arg f  : x = y → f x = f y)
#check (left_distrib x y z : x * (y + z) = x * y + x * z)
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (neg_mul 1 x : -1 * x = -(1 * x))
#check (neg_mul_neg x y : -x * -y = x * y)
#check (neg_neg x : - -x = x)
#check (neg_one_sq : (-1)^2 = 1)
#check (one_add_one_eq_two : 1 + 1 = 2)
#check (one_le_two : 1 ≤ 2)
#check (one_lt_two : (1 : ℝ) < 2)
#check (one_mul x : 1 * x = x)
#check (one_mul x : 1 * x = x)
#check (one_pow n : 1 ^ n = 1)
#check (pow_mul x m n : x ^ (m * n) = (x ^ m) ^ n)
#check (pow_succ x n : x ^ (n + 1) = x ^ n * x)
#check (sub_add_add_cancel x y z : (x - z) + (y + z) = x + y)
#check (sub_eq_add_neg x y : x - y = x + -y)
