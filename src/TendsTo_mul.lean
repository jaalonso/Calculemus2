-- TendsTo_mul.lean
-- If uₙ tends to a y vₙ tends to b, then uₙvₙ tends to ab
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, December 2, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, a sequence u₀, u₁, u₂, ... can be represented by a function
-- (u : ℕ → ℝ) such that u(n) is uₙ.
--
-- It is defined that the sequence u tends to c by:
--    def TendsTo (u : ℕ → ℝ) (c : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε
--
-- Prove that if uₙ tends to a and vₙ tends to b, then uₙvₙ
-- tends to ab.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- The proof will rely on the following lemmas proved in previous
-- exercises:
-- + Lemma 1. The sequence uₙ tends to a if and only if uₙ-a tends to 0.
-- + Lemma 2. If uₙ and vₙ tends to 0, then uₙvₙ tends to 0.
-- + Lemma 3. If uₙ tends to a and c ∈ ℝ, then cuₙ tends to ca.
-- + Lemma 4. If uₙ tends to a and c ∈ ℝ, then uₙc tends to ac.
-- + Lemma 5. If uₙ tends to a and vₙ to b, then uₙ+vₙ tends to a+b.
--
-- By Lemma 1, since lim uₙ = a and lim vₙ = b, it follows that
--    lim (uₙ - a) = 0                                             (1)
--    lim (vₙ - b) = 0                                             (2)
-- By Lemma 2, (1) and (2), it follows that
--    lim (uₙ - a)(vₙ - b) = 0                                     (3)
-- By Lemma 3 and (2), it follows that
--    lim a(vₙ - b) = a·0                                          (4)
-- By Lemma 4 and (1), it follows that
--    lim (uₙ - a)b = 0·b                                          (5)
-- By Lemma 5, (3), (4), and (5), it follows that
--    lim ((uₙ-a)(vₙ-b)+a·(vₙ-b)+(uₙ-a)·b) = 0+t·0+0·u
-- and, simplifying, we have
--    lim (uₙvₙ - ab) = 0
-- Finally, by Lemma 1,
--    lim uₙvₙ = ab

-- Proofs with Lean4
-- =================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}
variable {a b : ℝ}

def TendsTo (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

-- Lema 1. The sequence uₙ tends to a if and only if uₙ-a tends to 0.
-- (See proofs in https://tinyurl.com/22nkht98)
lemma TendsTo_iff :
  TendsTo u a ↔ TendsTo (fun i ↦ u i - a) 0 :=
by
  rw [iff_eq_eq]
  calc TendsTo u a
       = ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε       := rfl
     _ = ∀ ε > 0, ∃ N, ∀ n ≥ N, |(u n - a) - 0| < ε := by simp
     _ = TendsTo (fun i ↦ u i - a) 0                := rfl

-- Lemma 2. If uₙ and vₙ tends to 0, then uₙvₙ tends to 0.
-- (See proofs in https://tinyurl.com/2ag9plvs )
lemma TendsTo_mul_cero
  (hu : TendsTo u 0)
  (hv : TendsTo v 0)
  : TendsTo (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  obtain ⟨U, hU⟩ := hu ε hε
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  obtain ⟨V, hV⟩ := hv 1 zero_lt_one
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n - 0| < ε
  -- hV : |v n - 0| < 1
  -- ⊢ |(u * v) n - 0| < ε
  calc |(u * v) n|
       = |u n * v n|
         := rfl
     _ = |u n| * |v n|
         := abs_mul (u n) (v n)
     _ < ε * 1
         := mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
     _ = ε
         := mul_one ε

-- Lemma 3. If uₙ tends to a and c ∈ ℝ, then cuₙ tends to ca. (See
-- proofs in https://tinyurl.com/2244qcxs )
lemma TendsTo_const_mul
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
    obtain ⟨N, hN⟩ := h
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
       _ < |c| * (ε / |c|) := (mul_lt_mul_iff_of_pos_left hc').mpr hN
       _ = ε               := mul_div_cancel₀ ε (ne_of_gt hc')

-- Lemma 4. If uₙ tends to a and c ∈ ℝ, then uₙc tends to ac. (See
-- proofs in https://tinyurl.com/2xr94fh4 )
lemma TendsTo_mul_const
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
  exact TendsTo_const_mul h

-- Lemma 5. If uₙ tends to a and vₙ to b, then uₙ+vₙ tends to a+b. (See
-- proofs in https://tinyurl.com/294wn94r )
lemma TendsTo_add
  (hu : TendsTo u a)
  (hv : TendsTo v b)
  : TendsTo (u + v) (a + b) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u + v) n - (a + b)| < ε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨Nu, hNu⟩ := hu (ε / 2) hε2
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), n ≥ Nu → |u n - a| < ε / 2
  obtain ⟨Nv, hNv⟩ := hv (ε / 2) hε2
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), n ≥ Nv → |v n - b| < ε / 2
  clear hu hv hε2 hε
  let N := max Nu Nv
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(s + t) n - (a + b)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have nNu : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n nNu
  -- hNu : |u n - a| < ε / 2
  have nNv : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n nNv
  -- hNv : |v n - b| < ε / 2
  clear hn nNu nNv
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  := rfl
     _ = |(u n - a) + (v n - b)|  := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|    := by apply abs_add_le
     _ < ε / 2 + ε / 2            := by linarith [hNu, hNv]
     _ = ε                        := by apply add_halves

-- Proof 1
-- =======

example
  (hu : TendsTo u a)
  (hv : TendsTo v b)
  : TendsTo (fun n ↦ u n * v n) (a * b) :=
by
  rw [TendsTo_iff] at *
  -- hu : TendsTo (fun i => u i - a) 0
  -- hv : TendsTo (fun i => v i - b) 0
  -- ⊢ TendsTo (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  have h1 : TendsTo (fun n => (u n - a) * (v n - b)) 0
    := TendsTo_mul_cero hu hv
  have h2 : TendsTo (fun n => a * (v n - b)) (a * 0)
    := TendsTo_const_mul hv
  have h3 : TendsTo (fun n => (u n - a) * b) (0 * b)
    := TendsTo_mul_const hu
  exact TendsTo_add (TendsTo_add h1 h2) h3

-- Proof 2
-- =======

example
  (hu : TendsTo u a)
  (hv : TendsTo v b)
  : TendsTo (fun n ↦ u n * v n) (a * b) :=
by
  rw [TendsTo_iff] at *
  -- hu : TendsTo (fun i => u i - a) 0
  -- hv : TendsTo (fun i => v i - b) 0
  -- ⊢ TendsTo (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  apply TendsTo_add
  . -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b)) (0 + a * 0)
    apply TendsTo_add
    . -- ⊢ TendsTo (fun i => (u i - a) * (v i - b)) 0
      exact TendsTo_mul_cero hu hv
    . -- ⊢ TendsTo (fun i => a * (v i - b)) (a * 0)
      exact TendsTo_const_mul hv
  . -- ⊢ TendsTo (fun i => (u i - a) * b) (0 * b)
    exact TendsTo_mul_const hu

-- Proof 3
-- =======

example
  (hu : TendsTo u a)
  (hv : TendsTo v b)
  : TendsTo (fun n ↦ u n * v n) (a * b) :=
by
  rw [TendsTo_iff] at *
  -- hu : TendsTo (fun i => u i - a) 0
  -- hv : TendsTo (fun i => v i - b) 0
  -- ⊢ TendsTo (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ TendsTo (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  refine' TendsTo_add (TendsTo_add _ _) _
  · -- ⊢ TendsTo (fun i => (u i - a) * (v i - b)) 0
    exact TendsTo_mul_cero hu hv
  · -- ⊢ TendsTo (fun i => a * (v i - b)) (a * 0)
    exact TendsTo_const_mul hv
  · -- ⊢ TendsTo (fun i => (u i - a) * b) (0 * b)
    exact TendsTo_mul_const hu

-- Used lemmas
-- ===========

variable (p q : Prop)
variable (c d x y: ℝ)
variable (f : ℝ → ℝ)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_nonneg a : 0 ≤ |a|)
#check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
#check (add_halves a : a / 2 + a / 2 = a)
#check (congr_arg f : x = y → f x = f y)
#check (div_pos : 0 < a → 0 < b → 0 < a / b)
#check (iff_eq_eq : (p ↔ q) = (p = q))
#check (le_of_max_le_left : max a b ≤ c → a ≤ c)
#check (le_of_max_le_right : max a b ≤ c → b ≤ c)
#check (mul_comm a b : a * b = b * a)
#check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
#check (mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d)
#check (mul_lt_mul_iff_of_pos_left : 0 < a → (a * b < a * c ↔ b < c))
#check (mul_one a : a * 1 = a)
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
#check (ne_of_gt : b < a → a ≠ b)
#check (zero_lt_one : 0 < 1)
