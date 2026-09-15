-- Reto_6.lean
-- Soluciones de 6º reto (14 de junio de 2026).
-- Teorema del emparedado: Si aₙ y cₙ convergen a L y aₙ ≤ bₙ ≤ cₙ para
--   todo n, entonces bₙ converge a L.
-- Sevilla, 14-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si las sucesiones a y c convergen a L, y b está
-- comprimida entre a y c (es decir, aₙ ≤ bₙ ≤ cₙ para todo n), entonces
-- b también converge a L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que existe un N tal que,
--    ∀ n ≥ N, |bₙ - L| < ε                                          (1)
--
-- Puesto que a y c convergen a L, existen N₁ y ℕ₂ tales que
--    ∀ n ≥ N₁, |aₙ - L| < ε                                         (2)
--    ∀ n ≥ N₂, |cₙ - L| < ε                                         (3)
-- Sea
--    N = máx(N₁, ℕ₂).                                               (4)
-- Para demostrar (1), sea n ≥ N. Por  (4), se tiene que
--    n ≥ N₁
--    n ≥ N₂
-- Luego, usando (2) y (3), se tiene que
--    |aₙ - L| < ε
--    |cₙ - L| < ε
-- de donde se deduce que
--    - ε < aₙ - L < ε                                               (5)
--    - ε < bₙ - L < ε                                               (6)
-- Luego,
--    -ε < aₙ - L   [por (5)]
--       ≤ bₙ - L   [por hipótesis de b]
--       ≤ cₙ - L   [por hipótesis de b]
--       < ε        [por (6)]
-- Por tanto,
--    -ε < bₙ - L < ε
-- y, finalmente,
--    |bₙ - L| < ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a b c : ℕ → ℝ}
variable {L : ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  exact ⟨max Na Nc, by grind⟩

-- 2ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := by grind
     _ ≤ b n - L := by grind
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := by grind
     _ < ε       := by grind

-- 3ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hc : LimSuc c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n) :
    LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  exact ⟨by linarith [hab n], by linarith [hbc n]⟩

-- 4ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hc : LimSuc c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n)
    : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  refine ⟨?_, ?_⟩
  · -- ⊢ -ε < b n - L
    calc -ε
         < a n - L := hna.1
       _ ≤ b n - L := by linarith [hab n]
  · calc b n - L
         ≤ c n - L := by linarith [hbc n]
       _ < ε       := hnc.2

-- 5ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : Na ≤ n := le_of_max_le_left hn
  have hnc : Nc ≤ n := le_of_max_le_right hn
  have hNa : |a n - L| < ε := hNa n hna
  have hNc : |c n - L| < ε := hNc n hnc
  rewrite [abs_lt] at hNa
  -- hNa : -ε < a n - L ∧ a n - L < ε
  rewrite [abs_lt] at hNc
  -- hNc : -ε < c n - L ∧ c n - L < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := hNa.1
     _ ≤ b n - L := sub_le_sub_right (hab n) L
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := sub_le_sub_right (hbc n) L
     _ < ε       := hNc.2
