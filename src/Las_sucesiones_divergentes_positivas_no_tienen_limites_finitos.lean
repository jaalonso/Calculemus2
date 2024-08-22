-- Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.lean
-- Las sucesiones divergentes positivas no_tienen límites finitos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite (u: ℕ → ℝ) (a: ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
--
-- La sucesión u diverge positivamente cuando, para cada número real A,
-- se puede encontrar un número natural m tal que si n ≥ m, entonces
-- uₙ > A. En Lean se puede definir por
--    def diverge_positivamente (u : ℕ → ℝ) :=
--      ∀ A, ∃ m, ∀ n ≥ m, u n > A
--
-- Demostrar que si u diverge positivamente, entonces ningún número real
-- es límite de u.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que existe un a ∈ ℝ tal que a es límite de u. Entonces,
-- existe un m₁ ∈ ℕ tal que
--    (∀ n ≥ m₁) |uₙ - a| < 1                                        (1)
-- Puesto que u diverge positivamente, existe un m₂ ∈ ℕ tal que
--    (∀ n ≥ m₂) uₙ > a + 1                                          (2)
-- Sea m el máximo de m₁ y m₂. Entonces,
--    m ≥ m₁                                                         (3)
--    m ≥ m₂                                                         (4)
-- Por (1) y (3), se tiene que
--    |uₘ - a| < 1
-- Luego,
--    uₘ - a < 1                                                     (5)
-- Por (2) y (4), se tiene que
--    uₘ > a + 1                                                     (6)
-- Por tanto,
--    uₘ < a + 1       [por (5)]
--       < uₘ          [por (6)]
-- De donde se tiene que
--    uₘ < uₘ
-- que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

-- 1ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 zero_lt_one with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  specialize hm1 m (le_max_left _ _)
  -- hm1 : |u m - a| < 1
  specialize hm2 m (le_max_right _ _)
  -- hm2 : u m > a + 1
  replace hm1 : u m - a < 1 := lt_of_abs_lt hm1
  replace hm2 : 1 < u m - a := lt_sub_iff_add_lt'.mpr hm2
  apply lt_irrefl (u m)
  -- ⊢ u m < u m
  calc u m < a + 1 := by exact sub_lt_iff_lt_add'.mp hm1
         _ < u m   := lt_sub_iff_add_lt'.mp hm2

-- 2ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 (by linarith) with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  replace hm1 : |u m - a| < 1 := by aesop
  replace hm1 : u m - a < 1   := lt_of_abs_lt hm1
  replace hm2 : a + 1 < u m   := by aesop
  replace hm2 : 1 < u m - a   := lt_sub_iff_add_lt'.mpr hm2
  apply lt_irrefl (u m)
  -- ⊢ u m < u m
  calc u m < a + 1 := by linarith
         _ < u m   := by linarith

-- 3ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 (by linarith) with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  specialize hm1 m (le_max_left _ _)
  -- hm1 : |u m - a| < 1
  rw [abs_lt] at hm1
  -- hm1 : -1 < u m - a ∧ u m - a < 1
  specialize hm2 m (le_max_right _ _)
  -- hm2 : u m > a + 1
  linarith

-- Lemas usados
-- ============

-- variable (m n : ℕ)
-- variable (a b c : ℝ)
-- #check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (lt_irrefl a : ¬a < a)
-- #check (lt_of_abs_lt : |a| < b → a < b)
-- #check (lt_sub_iff_add_lt' : b < c - a ↔ a + b < c)
-- #check (sub_lt_iff_lt_add' : a - b < c ↔ a < b + c)
-- #check (zero_lt_one : 0 < 1)
