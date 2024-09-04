-- Sufficient_condition_of_continuity.lean
-- If f is continuous at a and the limit of u(n) is a, then the limit of f(u(n)) is f(a).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 4, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, we can define that a is the limit of the sequence u by:
--    def is_limit (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- and that f is continuous at a by:
--    def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
--
-- To prove that if the function f is continuous at the point a, and the
-- sequence u(n) converges to a, then the sequence f(u(n)) converges to
-- f(a).
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- Let ε > 0. We need to prove that there exists a k ∈ ℕ such that for
-- all n ≥ k,
--    |(f ∘ u)(n) - f(a)| ≤ ε                                        (1)
--
-- Since f is continuous at a, there exists a δ > 0 such that
--    |x - a| ≤ δ → |f(x) - f(a)| ≤ ε                                (2)
-- Furthermore, because the is_limit of u(n) is a, there exists a k ∈ ℕ
-- such that for all n ≥ k,
--   |u(n) - a| ≤ δ                                                 (3)
--
-- To prove (1), let n ∈ ℕ such that n ≥ k. Then,
--   |(f ∘ u)(n) - f(a)| = |f(u(n)) - f(a)|
--                       ≤ ε                           [by (2) and (3)]

-- Proofs with Lean4
-- =================

import Mathlib.Data.Real.Basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

-- Proof 1
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  calc |(f ∘ u) n - f a| = |f (u n) - f a| := by simp only [Function.comp_apply]
                       _ ≤ ε               := hδ2 (u n) (hk n hn)

-- Proof 2
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- Proof 3
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  apply hδ2
  -- ⊢ |u n - a| ≤ δ
  exact hk n hn

-- Proof 4
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- Used lemmas
-- ===========

-- variable (g : ℝ → ℝ)
-- variable (x : ℝ)
-- #check (Function.comp_apply : (g ∘ f) x = g (f x))
