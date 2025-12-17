-- Limit_of_7u.lean
-- If u(n) tends to a, then 7u(n) tends to 7a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, November 7, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean, a sequence  u₀, u₁, u₂, ... can be represented by a function
-- (u : ℕ → ℝ) such that u(n) is the term uₙ.
--
-- We define that u tends to a by
--    def tendsTo : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Prove that if uₙ tends to a, then 7uₙ tends to 7a.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let ε > 0. We need to prove that there exists an N ∈ ℕ such that
--    (∀ n ∈ ℕ)[N ≤ n → |7u(n) - 7a| < ε]                              (1)
-- Since u(n) tends to a, there exists an N ∈ ℕ such that
--    (∀ n ∈ ℕ)[N ≤ n → |u(n) - a| < ε/7]                              (2)
-- Let N ∈ ℕ that satisfies (2), let's see that the same N satisfies
-- (1). For this, let n ∈ ℕ such that N ≤ n. Then,
--    |7u(n) - 7a| = |7(u(n) - a)|
--                 = |7||u(n) - a|
--                 = 7|u(n) - a|
--                 < 7(ε / 7)        [by (2)]
--                 = ε

-- Proofs with Lean4
-- =================

import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a : ℝ}

def tendsTo : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- Proof 1
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  specialize h (ε / 7) (by linarith)
  -- h : ∃ N, ∀ n ≥ N, |u n - a| < ε / 7
  obtain ⟨N, hN⟩ := h
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  calc |7 * u n - 7 * a|
     = |7 * (u n - a)|    := by rw [← mul_sub]
   _ = |7| * |u n - a|    := by rw [abs_mul]
   _ = 7 * |u n - a|      := by congr ; simp [Nat.abs_ofNat]
   _ < 7 * (ε / 7)        := by simp [Nat.ofNat_pos, hN]
   _ = ε                  := mul_div_cancel₀ ε (OfNat.zero_ne_ofNat 7).symm

-- Proof 2
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  obtain ⟨N, hN⟩ := h (ε / 7) (by linarith)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  rw [← mul_sub]
  -- ⊢ |7 * (u n - a)| < ε
  rw [abs_mul]
  -- ⊢ |7| * |u n - a| < ε
  rw [abs_of_nonneg]
  . -- ⊢ 7 * |u n - a| < ε
    linarith
  . -- ⊢ 0 ≤ 7
    exact Nat.ofNat_nonneg' 7

-- Proof 3
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  obtain ⟨N, hN⟩ := h (ε / 7) (by linarith)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;> linarith

-- Used lemmas
-- ===========

variable (b c : ℝ)
variable (n : ℕ)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_of_nonneg : 0 ≤ a → |a| = a)
#check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
