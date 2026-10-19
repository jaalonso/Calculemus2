-- Reto_23.lean
-- La sucesión constante aₙ = L converge a L.
-- Sevilla, 12-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que La sucesión constante aₙ = L converge a L.
--
-- Para ello, completar la siguiente teoría en Lean 4:
--    import Mathlib.Tactic
--
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |a n - L| < ε
--
--    variable {a : ℕ → ℝ}
--    variable {L : ℝ}
--
--    example
--      (h : ∀ n, a n = L)
--      : LimSuc a L :=
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada ε ∈ ℝ tal que ε > 0, existe
-- un k ∈ ℕ, tal que
--    ∀ n ≥ k, |aₙ - L| < ε
-- Tomamos k = 0. Para todo n ≥ k, como aₙ = L, se tiene
--    |aₙ - L| = |L - L|
--             = |0|
--             = 0
--             < ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |a n - L| < ε

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  grind

-- 2ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  refine ⟨0, by grind⟩

-- 3ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
fun _ _ => ⟨0, by grind⟩

-- 4ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  rintro n -
  -- n : ℕ
  -- ⊢ |a n - L| < ε
  calc |a n - L|
     = |L - L|    := by grind
   _ = 0          := by grind
   _ < ε          := by grind

-- 5ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  rintro n -
  -- n : ℕ
  -- ⊢ |a n - L| < ε
  calc |a n - L|
     = |L - L|    := by rw [h n]
   _ = 0          := by norm_num
   _ < ε          := hε

-- 6ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  rintro n -
  -- n : ℕ
  -- ⊢ |a n - L| < ε
  calc |a n - L|
     = |L - L|    := by rw [h]
   _ = |0|        := by rw [sub_self L]
   _ = 0          := abs_zero
   _ < ε          := hε

-- 7ª demostración
-- ===============

theorem limSuc_const
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  rintro n -
  -- n : ℕ
  -- ⊢ |a n - L| < ε
  calc |a n - L|
     = |L - L|    := congrArg (|· - L|) (h n)
   _ = |0|        := congrArg abs (sub_self L)
   _ = 0          := abs_zero
   _ < ε          := hε

-- Lemas usados
-- ============

-- #check (abs_zero : |(0 : ℝ)| = 0)
-- #check (sub_self L : L - L = 0)
