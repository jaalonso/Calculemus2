-- Reto_9.lean
-- Soluciones del 9º reto (6 de julio de 2026).
-- Unicidad del límite.
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ converge tanto a L como a
-- M, entonces L = M.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que si aₙ es una sucesión y L y M son
-- límites de aₙ, entonces L = M. Lo haremos por
-- contradicción. Para ello, supongamos que
--    L ≠ M
-- Sea
--    ε = |L - M|                                          (1)
-- Entonces,
--    ε/2 > 0                                              (2)
-- y, teniendo en cuenta que aₙ converge a L y a M, existen
-- k₁ y k₂ tales que
--    ∀ n ≥ k₁, |aₙ - L| < ε/2                             (3)
--    ∀ n ≥ k₂, |aₙ - M| < ε/2                             (4)
-- Sea,
--    k = máx(k₁, k₂)                                      (5)
-- Entonces,
--    k ≥ k₁                                               (6)
--    k ≥ k₂                                               (7)
-- De (3) y (6), se tiene
--    |aₖ - L| < ε/2                                       (8)
-- De (4) y (7), se tiene
--    |aₖ - M| < ε/2                                       (9)
--
-- Tenemos que demostrar una contradicción, para lo que basta
-- probar que ε < ε. Se prueba mediante la siguiente cadena
--    ε = |L - M|                 [por (1)]
--      = |(L - M) + (aₖ - aₖ)|
--      = |(L - aₖ) + (aₖ - M)|
--      ≤ |L - aₖ| + |aₖ - M|
--      = |aₖ - L| + |aₖ - M|
--      < ε/2 + ε/2               [por (8) y (9)]
--      = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

variable {a : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by grind
       _ = |(L - a k) + (a k - M)| := by grind
       _ ≤ |L - a k| + |a k - M|   := by grind
       _ = |a k - L| + |a k - M|   := by grind
       _ < ε/2 + ε/2               := by grind
       _ = ε                       := by grind

-- 2ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  calc ε = |(L - a k) + (a k - M)| := by grind
       _ < ε                       := by grind

-- 3ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  have h1 : 0 < ε/2 := half_pos (abs_sub_pos.mpr h)
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  have h2 : k ≥ k1 := le_max_left k1 k2
  have h3 : k ≥ k2 := le_max_right k1 k2
  have h4 : |a k - L| < ε/2 := hk1 k h2
  have h5 : |a k - M| < ε/2 := hk2 k h3
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by ring_nf
       _ = |(L - a k) + (a k - M)| := by ring_nf
       _ ≤ |L - a k| + |a k - M|   := abs_add_le (L - a k) (a k - M)
       _ = |a k - L| + |a k - M|   := by congr 1 ; exact abs_sub_comm L (a k)
       _ < ε/2 + ε/2               := add_lt_add h4 h5
       _ = ε                       := by ring

-- 4ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  have h1 : 0 < ε/2 := half_pos (abs_sub_pos.mpr h)
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  have h2 : k ≥ k1 := le_max_left k1 k2
  have h3 : k ≥ k2 := le_max_right k1 k2
  have h4 : |a k - L| < ε/2 := hk1 k h2
  have h5 : |a k - M| < ε/2 := hk2 k h3
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + 0|           := congrArg abs (add_zero (L - M)).symm
       _ = |(L - M) + (a k - a k)| := congrArg (|(L - M) + ·|) (sub_self (a k)).symm
       _ = |(L - a k) + (a k - M)| := congrArg abs (by ring)
       _ ≤ |L - a k| + |a k - M|   := abs_add_le (L - a k) (a k - M)
       _ = |a k - L| + |a k - M|   := congrArg (· + |a k - M|) (abs_sub_comm L (a k))
       _ < ε/2 + ε/2               := add_lt_add h4 h5
       _ = ε                       := add_halves ε

-- Lemas usados
-- ============

namespace Lemas

variable (a b c d : ℝ)
variable (f : ℝ → ℝ)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (abs_sub_comm a b : |a - b| = |b - a|)
#check (abs_sub_pos : 0 < |a - b| ↔ a ≠ b)
#check (add_halves a : a / 2 + a / 2 = a)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (add_zero a : a + 0 = a)
#check (congrArg f : a = b → f a = f b)
#check (half_pos : a > 0 → a / 2 > 0)
#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (lt_irrefl a : ¬a < a)
#check (sub_ne_zero_of_ne : a ≠ b → a - b ≠ 0)
#check (sub_self a : a - a = 0)

end Lemas
