-- Si_a_converge_a_L_entonces_2a_converge_a_2L.lean
-- Si a(n) converge a L, entonces 2a(n) converge a 2L
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-mayo-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a(n) converge a L, entonces 2a(n) converge a 2L.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si aₙ converge a L, entonces 2aₙ converge a 2L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea bₙ la suceción definida por
--    bₙ = 2aₙ                                                        (1)
-- Tenemos que demostrar que para cada ε > 0, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, |bₙ - 2L| < ε                                          (2)
-- Puesto que aₙ converge a L, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, |aₙ - L| < ε/2                                         (3)
-- Veamos que N también cumple (2). En efecto, sea n ≥ N. Entonces
--    |bₙ - 2L| = |2aₙ - 2L|     [por (1)]
--              = 2|aₙ - L|
--              < 2ε/2           [por (3)]
--              = ε

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a b : ℕ → ℝ}
variable {L : ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  obtain  ⟨N, hN⟩ := ha (ε / 2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  grind

-- 2ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  obtain  ⟨N, hN⟩ := ha (ε / 2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := by grind
     _ = |2 * (a n - L)|   := by grind
     _ = 2 * |a n - L|     := by grind
     _ < 2 * ε / 2         := by grind
     _ = ε                 := by grind

-- 3ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  obtain  ⟨N, hN⟩ := ha (ε / 2) (half_pos hε)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := by rw [hb n]
     _ = |2 * (a n - L)|   := by simp only [mul_sub]
     _ = |2| * |a n - L|   := by simp only [abs_mul]
     _ = 2 * |a n - L|     := by simp only [abs_two]
     _ < 2 * (ε / 2)       := by simp only [ mul_lt_mul_of_pos_left, hN n hn, two_pos]
     _ = ε                 := by rw [mul_div_cancel₀ ε two_ne_zero]

-- 4ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  obtain  ⟨N, hN⟩ := ha (ε / 2) (half_pos hε)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := congr_arg (|· - 2 * L|) (hb n)
     _ = |2 * (a n - L)|   := congr_arg abs (mul_sub 2 (a n) L).symm
     _ = |2| * |a n - L|   := abs_mul 2 (a n - L)
     _ = 2 * |a n - L|     := congr_arg (· * |a n - L|) abs_two
     _ < 2 * (ε / 2)       := mul_lt_mul_of_pos_left (hN n hn) two_pos
     _ = ε                 := mul_div_cancel₀ ε two_ne_zero

-- Lemas usados
-- ============

variable (x y z : ℝ)

#check (abs_mul x y : |x * y| = |x| * |y|)
#check (abs_two : |(2 : ℝ)| = 2)
#check (half_pos : 0 < x → 0 < x / 2)
#check (mul_div_cancel₀ x : y ≠ 0 → y * (x / y) = x)
#check (mul_lt_mul_of_pos_left : x < y → 0 < z → z * x < z * y)
#check (mul_sub x y z : x * (y - z) = x * y - x * z)
#check (two_ne_zero : 2 ≠ 0)
#check (zero_lt_two : 0 < 2)
