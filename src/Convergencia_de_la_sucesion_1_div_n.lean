-- Reto_1.lean
-- Soluciones del 1º reto (10 de mayo de 2026)
-- La sucesión 1/n converge a 0.
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- En Lean, una sucesión a₀,a₁,a₂,... se puede representar
-- mediante una función  (a : ℕ → ℝ) de forma que a(n) es aₙ.
--
-- Se define que L es el límite de la sucesión a, por
--
-- def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--   ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
-- Demostrar que si para todo n, aₙ=1/n, entonces la sucesión
-- a converge a 0.
--
-- Para ello, completar la siguiente teoría de Lean 4:
--
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Tactic
--
-- variable (a : ℕ → ℝ)
--
-- def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--   ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
-- example
--   (ha : ∀ n, a n = 1 / n)
--   : LimSuc a 0 :=
-- by sorry
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Por la propiedad arquimediana,
-- existe k ∈ ℕ tal que
--    1 / ε < k                                            (1)
-- Veamos que, para todo n ≥ k, |a(n) - 0| < ε. En efecto, sea
--    n ≥ k                                                (2)
-- Entonces,
--    |a(n) - 0| = |1/n - 0|
--               = 1/n
--               ≤ 1/k          [por (2)]
--               < ε            [por (1)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- 1ª solución
-- ===========

namespace Solucion1

lemma L1
  {ε : ℝ}
  (hε : ε > 0)
  {k : ℕ}
  (hk : 1 / ε < k)
  : 0 < (k : ℝ) :=
(one_div_pos.mpr hε).trans hk

lemma L2
  {ε : ℝ}
  (hε : ε > 0)
  {k : ℕ}
  (hk : 1 / ε < k)
  : 1 / (k : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑k
    gcongr
  · -- ⊢ 0 < ε
    gcongr
  · -- ⊢ 0 < ↑k
    exact L1 hε hk

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |a n - 0| < ε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  -- k : ℕ
  -- hk : 1 / ε < ↑k
  use k
  --⊢ ∀ n ≥ k, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n - 0| < ε
  calc
      |a n - 0|
      = |a n|         := by grind
    _ = |1 / (n : ℝ)| := by grind
    _ = 1 / n         := by grind
    _ ≤ 1 / k         := by gcongr ; exact L1 hε hk
    _ < ε             := L2 hε hk

end Solucion1

-- 2ª solución
-- ===========

namespace Solucion2

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

lemma L3
  {ε : ℝ}
  (hε : ε > 0)
  {k : ℕ}
  (hk : 1 / ε < k)
  : 0 < (k : ℝ) :=
by calc
  (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  _       < k     := hk

lemma L4
  {ε : ℝ}
  (hε : ε > 0)
  {k n : ℕ}
  (hk : 1 / ε < k)
  (hn : n ≥ k)
  : 1 / (n : ℝ) ≤ 1 / (k : ℝ) :=
by
  apply one_div_le_one_div_of_le
  · -- ⊢ 0 < ↑k
    exact L3 hε hk
  · -- ⊢ ↑k ≤ ↑n
    exact Nat.cast_le.mpr hn

lemma L5
  {ε : ℝ}
  (hε : ε > 0)
  {k : ℕ}
  (hk : 1 / ε < k)
  : 1 / (k : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑k
    exact RCLike.ofReal_lt_ofReal.mp hk
  · -- ⊢ 0 < ε
    exact RCLike.ofReal_pos.mp hε
  · -- ⊢ 0 < ↑k
    exact L3 hε hk

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |a n - 0| < ε
  have h1 : ∃ (k : ℕ), 1 / ε < k := exists_nat_gt (1 / ε)
  obtain ⟨k, hk⟩ := h1
  -- k : ℕ
  -- hk : 1 / ε < ↑k
  use k
  -- ⊢ ∀ n ≥ k, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n - 0| < ε
  calc |a n - 0|
       = |a n|         := by simp [sub_zero]
     _ = |1 / (n : ℝ)| := by rw [ha]
     _ = 1 / n         := L2
     _ ≤ 1 / k         := L4 hε hk hn
     _ < ε             := L5 hε hk

end Solucion2
