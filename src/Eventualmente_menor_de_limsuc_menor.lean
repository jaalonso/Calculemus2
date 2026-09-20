-- Reto_12.lean
-- Soluciones del reto nº. 12 (27 de julio de 2026).
-- Si aₙ → L, bₙ → M y L < M, entonces eventualmente aₙ < bₙ.
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si las sucesiones aₙ y bₙ convergen a L y M,
-- respectivamente, con L < M, entonces eventualmente
-- aₙ < bₙ; es decir, que existe un k ∈ ℕ tal que, para todo
-- n ≥ k, aₙ < bₙ.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    ε = (M - L) / 2                                      (1)
-- Puesto que L < M, se tiene que ε > 0. Y, usando las
-- convergencias de  aₙ y bₙ, se tiene que existen k₁ y k₂
-- tales que
--    ∀ n ≥ k₁, |aₙ - L| < ε                               (2)
--    ∀ n ≥ k₂, |bₙ - M| < ε                               (3)
-- Sea
--    k = máx(k₁, k₂)                                      (4)
-- Veamos que
--    ∀ n ≥ k, aₙ < bₙ
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ k.                                               (5)
-- Entonces, por (4) y (5), se tiene que
--    n ≥ k₁
-- Luego, por (2), se tiene que
--    |aₙ - L| < ε
-- y, por consiguiente,
--    aₙ - L < ε                                           (6)
--
-- También, por (4) y (5), se tiene que
--    n ≥ k₂
-- Luego, por (3), se tiene que
--    |bₙ - M| < ε
-- y, por consiguiente,
--    -ε < bₙ - M                                          (7)
--
-- Finalmente,
--    a n < ε + L               [por (6)]
--        = (M - L) / 2 + L     [por (1)]
--        = (L + M) / 2
--        = -((M - L) / 2) + M
--        = -ε + M              [por (1)]
--        < b n                 [por (7)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

variable {a b : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  obtain ⟨k1, hk1⟩ := ha ε (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  use max k1 k2
  -- ⊢ ∀ n ≥ max k1 k2, a n < b n
  grind

-- 2ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  obtain ⟨k1, hk1⟩ := ha ε (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  use max k1 k2
  -- ⊢ ∀ n ≥ max k1 k2, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max k1 k2
  -- ⊢ a n < b n
  calc
    a n
    < ε + L              := by grind
  _ = (M - L) / 2 + L    := by grind
  _ = (L + M) / 2        := by grind
  _ = -((M - L) / 2) + M := by grind
  _ = -ε + M             := by grind
  _ < b n                := by grind

-- 3ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hb : LimSuc b M)
    (hLM : L < M) :
    ∃ k, ∀ n ≥ k, a n < b n := by
  set ε := (M - L) / 2 with ε_def
  -- ε_def : ε = (M - L) / 2
  obtain ⟨k1, hk1⟩ := ha ε (by positivity)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε (by positivity)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ a n < b n
  have h1 : n ≥ k1 := le_of_max_le_left hn
  have h2 : |a n - L| < ε := hk1 n h1
  have h3 : a n - L < ε := lt_of_abs_lt h2
  have h4 : n ≥ k2 := le_of_max_le_right hn
  have h5 : |b n - M| < ε := hk2 n h4
  have h6 : -ε < b n - M := neg_lt_of_abs_lt h5
  calc
    a n
    < ε + L              := lt_add_of_tsub_lt_right h3
  _ = (M - L) / 2 + L    := by rw [ε_def]
  _ = (L + M) / 2        := by ring
  _ = -((M - L) / 2) + M := by ring
  _ = -ε + M             := by rw [ε_def]
  _ < b n                := lt_tsub_iff_right.mp h6

-- 4ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2 with ε_def
  -- ε_def : ε = (M - L) / 2
  have hε : ε > 0 := half_pos (sub_pos_of_lt hLM)
  obtain ⟨k1, hk1⟩ := ha ε hε
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε hε
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ a n < b n
  have h1 : n ≥ k1 := le_of_max_le_left hn
  have h2 : |a n - L| < ε := hk1 n h1
  have h3 : a n - L < ε := lt_of_abs_lt h2
  have h4 : n ≥ k2 := le_of_max_le_right hn
  have h5 : |b n - M| < ε := hk2 n h4
  have h6 : -ε < b n - M := neg_lt_of_abs_lt h5
  calc
    a n
    < ε + L              := lt_add_of_tsub_lt_right h3
  _ = (M - L) / 2 + L    := congrArg (· + L) ε_def
  _ = (L + M) / 2        := by ring
  _ = -((M - L) / 2) + M := by ring
  _ = -ε + M             := congrArg (-· + M) ε_def
  _ < b n                := lt_tsub_iff_right.mp h6

-- 5ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  obtain ⟨k1, hk1⟩ := ha ε (by grind)
  obtain ⟨k2, hk2⟩ := hb ε (by grind)
  exact ⟨max k1 k2, fun _ _ => by grind⟩
