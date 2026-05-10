-- Convergencia_de_la_sucesion_1_div_n.lean
-- La sucesión aₙ = 1/n converge a 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-abril-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una sucesión tal que para todo n, a(n) = 1/n,
-- entonces a converge a 0.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Por la propiedad arquimediana, existe N ∈ ℕ
-- tal que
--    1 / ε < N                                                      (1)
-- Veamos que, para todo n ≥ N, |a(n) - 0| < ε. En efecto, sea
--    n ≥ N                                                          (2)
-- Entonces,
--    |a(n) - 0| = |1/n - 0|
--               = 1/n
--               ≤ 1/N          [por (2)]
--               < ε            [por (1)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

lemma L1
  {n : ℕ}
  : 0 ≤ 1 / (n : ℝ) :=
by
  -- ⊢ 0 ≤ 1 / ↑n
  apply div_nonneg
  · -- ⊢ 0 ≤ 1
    exact zero_le_one
  · -- ⊢ 0 ≤ ↑n
    exact Nat.cast_nonneg n

lemma L2
  {n : ℕ}
  : |1 / (n : ℝ)| = 1 / n :=
by
  apply abs_of_nonneg
  -- ⊢ 0 ≤ 1 / ↑n
  exact L1

variable {ε : ℝ}
variable {N : ℕ}

lemma L3
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 0 < (N : ℝ) :=
by calc
  (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  _       < N     := hN

lemma L4
  (hε : ε > 0)
  {n : ℕ}
  (hN : 1 / ε < N)
  (hn : n ≥ N)
  : 1 / (n : ℝ) ≤ 1 / (N : ℝ) :=
by
  apply one_div_le_one_div_of_le
  · -- ⊢ 0 < ↑N
    exact L3 hε hN
  · -- ⊢ ↑N ≤ ↑n
    exact Nat.cast_le.mpr hn

lemma L5
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 1 / (N : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑N
    exact RCLike.ofReal_lt_ofReal.mp hN
  · -- ⊢ 0 < ε
    exact RCLike.ofReal_pos.mp hε
  · -- ⊢ 0 < ↑N
    exact L3 hε hN

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  have h1 : ∃ (N : ℕ), 1 / ε < N := exists_nat_gt (1 / ε)
  choose N hN using h1
  -- N : ℕ
  -- hN : 1 / ε < ↑N
  use N
  -- ⊢ ∀ n ≥ N, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |a n - 0| < ε
  calc |a n - 0|
       = |a n|         := by simp [sub_zero]
     _ = |1 / (n : ℝ)| := by rw [ha]
     _ = 1 / n         := L2
     _ ≤ 1 / N         := L4 hε hN hn
     _ < ε             := L5 hε hN

-- 2ª demostración
-- ===============

lemma L6
  {n : ℕ}
  : |1 / (n : ℝ)| = 1 / n :=
by
  apply abs_of_nonneg
  -- ⊢ 0 ≤ 1 / ↑n
  positivity

lemma L7
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 0 < (N : ℝ) :=
by calc
  (0 : ℝ) < 1 / ε := by positivity
  _       < N     := hN

lemma L8
  (hε : ε > 0)
  {n : ℕ}
  (hN : 1 / ε < N)
  (hn : n ≥ N)
  : 1 / (n : ℝ) ≤ 1 / (N : ℝ) :=
by
  apply one_div_le_one_div_of_le
  · -- ⊢ 0 < ↑N
    exact L3 hε hN
  · -- ⊢ ↑N ≤ ↑n
    gcongr

lemma L9
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 1 / (N : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑N
    gcongr
  · -- ⊢ 0 < ε
    gcongr
  · -- ⊢ 0 < ↑N
    exact L3 hε hN

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  have h1 : ∃ (N : ℕ), 1 / ε < N := exists_nat_gt (1 / ε)
  choose N hN using h1
  -- N : ℕ
  -- hN : 1 / ε < ↑N
  use N
  --⊢ ∀ n ≥ N, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |a n - 0| < ε
  calc |a n - 0|
       = |a n|         := by norm_num
     _ = |1 / (n : ℝ)| := by rw [ha]
     _ = 1 / n         := L6
     _ ≤ 1 / N         := L8 hε hN hn
     _ < ε             := L9 hε hN

-- Lemas usados
-- ============

variable (x y : ℝ)
variable (m n : ℕ)
#check (Nat.cast_le : ↑m ≤ ↑n ↔ m ≤ n)
#check (Nat.cast_nonneg n : 0 ≤ n)
#check (RCLike.ofReal_lt_ofReal : ↑x < ↑y ↔ x < y)
#check (abs_of_nonneg : 0 ≤ x → |x| = x)
#check (div_nonneg : 0 ≤ x -> 0 ≤ y -> 0 ≤ x / y)
#check (exists_nat_gt x : ∃ n : ℕ, x < n)
#check (one_div_le_one_div_of_le : 0 < x → x ≤ y → 1 / y ≤ 1 / x)
#check (one_div_lt : 0 < x → 0 < y → (1 / x < y ↔ 1 / y < x))
#check (one_div_pos : 0 < 1 / x ↔ 0 < x)
#check (zero_le_one : 0 ≤ 1)
