-- Reto_20.lean
-- Si aₙ → L y M es una cota superior de aₙ, entonces L ≤ M.
-- Sevilla, 21-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si la sucesión aₙ converge a L y M es una cota
-- superior de aₙ (es decir, aₙ ≤ M para todo n), entonces L ≤ M.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostramos por contradicción. Supongamos que
--    L > M                                                    (1)
-- y llegaremos a la contradicción M < M.
--
-- De (1), se tiene
--    L - M > 0
-- y, usando esta cantidad en la convergencia de aₙ, se obtiene
-- un k tal que
--    ∀ n ≥ k, |aₙ - L| < L - M                                (2)
-- En particular, para n = k (que satisface k ≥ k), de (2) se
-- obtiene
--    |aₖ - L| < L - M                                         (3)
-- Además,
--    L - aₖ ≤ |aₖ - L|                                        (4)
-- ya que
--    L - aₖ = -(aₖ - L)
--           ≤ |aₖ - L|
-- Finalmente,
--    M = L - (L - M)
--      < L - |aₖ - L|  [por (3)]
--      ≤ L - (L - aₖ)  [por (4)]
--      = aₖ
--      ≤ M             [porque M es cota superior de aₙ]
-- Por tanto, M < M.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def CotaSup (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, a n ≤ M

variable {a : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hM : CotaSup a M)
  : L ≤ M :=
by
  by_contra hL
  -- hL : ¬L ≤ M
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  obtain ⟨k, hk⟩ := ha (L - M) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < L - M
  calc M
       < a k := by grind
     _ ≤ M   := hM k

-- 2ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hM : CotaSup a M)
  : L ≤ M :=
by
  by_contra hL
  -- hL : ¬L ≤ M
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  have h1 : L > M := not_le.mp hL
  have h2 : L - M > 0 := sub_pos.mpr h1
  obtain ⟨k, hk⟩ := ha (L - M) h2
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < L - M
  calc M
       = L - (L - M)    := by grind
     _ < L - |a k - L|  := by grind
     _ ≤ L - (L - a k)  := by grind
     _ = a k            := by grind
     _ ≤ M              := hM k

-- 3ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hM : CotaSup a M)
  : L ≤ M :=
by
  by_contra hL
  -- hL : ¬L ≤ M
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  have h1 : L - M > 0 := sub_pos.mpr (not_le.mp hL)
  obtain ⟨k, hk⟩ := ha (L - M) h1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < L - M
  have h2 : |a k - L| < L - M := hk k (le_refl k)
  have h3 : L - a k ≤ |a k - L| := by
    calc L - a k
         = -(a k - L) := by ring
       _ ≤ |a k - L|  := neg_le_abs (a k - L)
  calc M
       = L - (L - M)    := by ring
     _ < L - |a k - L|  := sub_lt_sub_left h2 L
     _ ≤ L - (L - a k)  := by gcongr
     _ = a k            := by ring
     _ ≤ M              := hM k

-- 4ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hM : CotaSup a M)
  : L ≤ M :=
by
  by_contra hL
  -- hL : ¬L ≤ M
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  obtain ⟨k, hk⟩ := ha (L - M) (sub_pos.mpr (not_le.mp hL))
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < L - M
  have h1 : |a k - L| < L - M := hk k (le_refl k)
  have h2 : L - a k ≤ |a k - L| := by
    calc L - a k
         = -(a k - L) := (neg_sub (a k) L).symm
       _ ≤ |a k - L|  := neg_le_abs (a k - L)
  calc M
       = L - (L - M)    := (sub_sub_self L M).symm
     _ < L - |a k - L|  := sub_lt_sub_left h1 L
     _ ≤ L - (L - a k)  := sub_le_sub_left h2 L
     _ = a k            := sub_sub_self L (a k)
     _ ≤ M              := hM k

-- Lemas usados
-- ============

variable (x y : ℝ)
#check (le_refl x : x ≤ x)
#check (lt_irrefl x : ¬x < x)
#check (neg_le_abs x : -x ≤ |x|)
#check (neg_sub x y : -(x - y) = y - x)
#check (not_le : ¬x ≤ y ↔ y < x)
#check (sub_le_sub_left : x ≤ y → ∀ z, z - y ≤ z - x)
#check (sub_lt_sub_left : x < y → ∀ z, z - y < z - x)
#check (sub_pos : 0 < x - y ↔ y < x)
#check (sub_sub_self x y : x - (x - y) = y)
