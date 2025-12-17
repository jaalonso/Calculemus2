-- Limit_multiplied_by_a_constant_2.lean
-- If the limit of the sequence u(n) is a and c ∈ ℝ, then the limit of
--   u(n)c is ac.
-- José A. Alonso Jiménez
-- Sevilla, 29 de noviembre de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean, a sequence u₀, u₁, u₂, ... can be represented by a function
-- (u : ℕ → ℝ) such that u(n) is uₙ.
--
-- It is defined that a is the limit of the sequence u, by
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Prove that if the limit of uₙ is a, then the limit of uₙc is ac.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- In a [previous exercise](https://tinyurl.com/2244qcxs) proofs have been
-- presented of the following property
--    "If the limit of the sequence uₙ is a and c ∈ ℝ, then the limit
--    of cuₙ is ca."
--
-- From this property, it is demonstrated that
--    "If the limit of the sequence uₙ is a and c ∈ ℝ, then the limit
--    of uₙc is ac."
-- Indeed, suppose that
--    the limit of uₙ is a
-- Then, by the previous property,
--    the limit of cuₙ is ca                                         (1)
-- But, by the commutativity of the product, we have that
--    (∀n ∈ ℕ)[cuₙ = uₙc]                                            (2)
--    ca = ac                                                        (3)
-- By (1), (2) and (3) we have that
--    the limit of uₙc is ac

-- Proof with Lean4
-- ================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u : ℕ → ℝ)
variable (a c : ℝ)

def TendsTo : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- The following theorem, demonstrated in a previous exercise, is used.
theorem tendsTo_const_mul
  (h : TendsTo u a)
  : TendsTo (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ TendsTo (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    calc |c * u n - c * a|
         = |c * (u n - a)| := congr_arg abs (mul_sub c (u n) a).symm
       _ = |c| * |u n - a| := abs_mul c  (u n - a)
       _ < |c| * (ε / |c|) := (mul_lt_mul_iff_right₀ hc').mpr hN
       _ = ε               := mul_div_cancel₀ ε (ne_of_gt hc')

example
  (h : TendsTo u a)
  : TendsTo (fun n ↦ (u n) * c) (a * c) :=
by
  have h1 : ∀ n, (u n) * c = c * (u n) := by
    intro
    -- n : ℕ
    -- ⊢ u n * c = c * u n
    ring
  have h2 : a * c = c * a := mul_comm a c
  simp [h1,h2]
  -- ⊢ TendsTo (fun n => c * u n) (c * a)
  exact tendsTo_const_mul u a c h

-- Used lemmas
-- ===========

variable (b c : ℝ)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
#check (div_pos : 0 < a → 0 < b → 0 < a / b)
#check (lt_div_iff₀' : 0 < c → (a < b / c ↔ c * a < b))
#check (mul_comm a b : a * b = b * a)
#check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
#check (mul_lt_mul_iff_right₀ : 0 < a → (a * b < a * c ↔ b < c))
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
