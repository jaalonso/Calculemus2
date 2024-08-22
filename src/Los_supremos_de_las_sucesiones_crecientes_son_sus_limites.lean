-- Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean
-- Los supremos de las sucesiones crecientes son sus límites
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea u una sucesión creciente. Demostrar que si S es un supremo de u,
-- entonces el límite de u es S.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que
--    (∃ m ∈ ℕ)(∀ n ∈ ℕ)[n ≥ m → |uₙ - S| ≤ ε]                       (1)
--
-- Por ser S un supremo de u, existe un k ∈ ℕ tal que
--    uₖ ≥ S - ε                                                     (2)
-- Vamos a demostrar que k verifica la condición de (1); es decir, que
-- si n ∈ ℕ tal que n ≥ k, entonces
--    |uₙ - S| ≤ ε
-- o, equivalentemente,
--    -ε ≤ uₙ - S ≤ ε
--
-- La primera desigualdad se tiene por la siguente cadena:
--    -ε = (S - ε) - S
--       ≤ uₖ - S         [por (2)]
--       ≤ uₙ - S         [porque u es creciente y n ≥ k]
--
-- La segunda desigualdad se tiene por la siguente cadena:
--    uₙ - S ≤ S - S      [porque S es un supremo de u]
--           = 0
--           ≤ ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u : ℕ → ℝ)
variable (S : ℝ)

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - c| ≤ ε

-- (supremo u S) expresa que el supremo de u es S.
def supremo (u : ℕ → ℝ) (S : ℝ) :=
  (∀ n, u n ≤ S) ∧ ∀ ε > 0, ∃ k, u k ≥ S - ε

-- 1ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  unfold supremo at hS
  -- hS : (∀ (n : ℕ), u n ≤ S) ∧ ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor
  . -- ⊢ -ε ≤ u n - S
    unfold Monotone at hu
    -- hu : ∀ ⦃a b : ℕ⦄, a ≤ b → u a ≤ u b
    specialize hu hn
    -- hu : u k ≤ u n
    calc -ε
         = (S - ε) - S := by ring
       _ ≤ u k - S     := sub_le_sub_right hk S
       _ ≤ u n - S     := sub_le_sub_right hu S
  . calc u n - S
         ≤ S - S       := sub_le_sub_right (hS₁ n) S
       _ = 0           := sub_self S
       _ ≤ ε           := le_of_lt hε

-- 2ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor
  . -- ⊢ -ε ≤ u n - S
    linarith [hu hn]
  . -- ⊢ u n - S ≤ ε
    linarith [hS₁ n]

-- 3ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor <;> linarith [hu hn, hS₁ n]

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b)
-- #check (le_of_lt : a < b → a ≤ b)
-- #check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
-- #check (sub_self a : a - a = 0)
