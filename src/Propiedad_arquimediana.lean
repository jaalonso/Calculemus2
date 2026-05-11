-- Propiedad_arquimediana.lean
-- Propiedad arquimediana de los números reales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-enero-2026
-- ---------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Demostrar la propiedad arquimediana de los números reales; es decir,
-- que para cualquier ε ∈ ℝ con 0 < ε, existe N ∈ ℕ tal que 1/ε < N.
-- ---------------------------------------------------------------------

variable {ε : ℝ}
variable (h : 0 < ε)

-- Demostración en lenguaje natural
-- ================================

-- Sea N = ⌈1/ε⌉₊ + 1. Entonces,
--    1/ε ≤ ⌈1/ε⌉₊
--        < ⌈1/ε⌉₊ + 1
--        = N
-- Por lo tanto, 1/ε < N.

-- 1ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
by
  -- ⊢ ∃ N, 1 / ε < ↑N
  use ⌈1 / ε⌉₊ + 1
  -- ⊢ 1 / ε < ↑(⌈1 / ε⌉₊ + 1)
  have fact : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
  -- fact : 1 / ε ≤ ↑⌈1 / ε⌉₊
  push_cast
  -- ⊢ 1 / ε < ↑⌈1 / ε⌉₊ + 1
  bound

-- 2ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
by
  -- ⊢ ∃ N, 1 / ε < ↑N
  use ⌈1 / ε⌉₊ + 1
  -- ⊢ 1 / ε < ↑(⌈1 / ε⌉₊ + 1)
  have fact : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil (1 / ε)
  -- fact : 1 / ε ≤ ↑⌈1 / ε⌉₊
  push_cast
  -- ⊢ 1 / ε < ↑⌈1 / ε⌉₊ + 1
  apply lt_of_le_of_lt fact
  -- ⊢ ↑⌈1 / ε⌉₊ < ↑⌈1 / ε⌉₊ + 1
  exact lt_add_one _

-- 3ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
by
  -- ⊢ ∃ N, 1 / ε < ↑N
  use ⌈1 / ε⌉₊ + 1
  -- ⊢ 1 / ε < ↑(⌈1 / ε⌉₊ + 1)
  push_cast
  -- ⊢ 1 / ε < ↑⌈1 / ε⌉₊ + 1
  calc
    1 / ε ≤ ↑⌈1 / ε⌉₊     := Nat.le_ceil (1 / ε)
    _     < ↑⌈1 / ε⌉₊ + 1 := lt_add_one _

-- 4ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
by
  -- ⊢ ∃ N, 1 / ε < ↑N
  use ⌈1 / ε⌉₊ + 1
  -- ⊢ 1 / ε < ↑(⌈1 / ε⌉₊ + 1)
  push_cast
  -- ⊢ 1 / ε < ↑⌈1 / ε⌉₊ + 1
  exact lt_of_le_of_lt (Nat.le_ceil (1 / ε)) (lt_add_one _)

-- 5ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
exists_nat_gt (1 / ε)

-- 6ª demostración
-- ===============

example : ∃ (N : ℕ), 1 / ε < N :=
by
  -- ⊢ ∃ N, 1 / ε < ↑N
  use ⌈1 / ε⌉₊ + 1
  -- ⊢ 1 / ε < ↑(⌈1 / ε⌉₊ + 1)
  calc
    1 / ε ≤ (⌈1 / ε⌉₊ : ℝ)     := Nat.le_ceil (1 / ε)
    _     < (⌈1 / ε⌉₊ : ℝ) + 1 := lt_add_one _
    _     = ↑(⌈1 / ε⌉₊ + 1)    := by norm_num

-- Lemas usados
-- ============

variable (a b c : ℝ)
#check (Nat.le_ceil a : a ≤ ↑⌈a⌉₊)
#check (exists_nat_gt (1 / ε) : ∃ n : ℕ, 1 / ε < ↑n)
#check (lt_add_one a : a < a + 1)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
