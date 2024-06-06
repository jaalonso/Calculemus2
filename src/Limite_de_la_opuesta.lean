-- Limite_de_la_opuesta.lean
-- Si el límite de la sucesión uₙ es a, entonces el límite de -uₙ es -a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que que si el límite de uₙ es a, entonces el de
-- -uₙ es -a.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que
--    (∃ N ∈ ℕ)(∀ n ≥ N)[|-uₙ - -a| < ε]                             (1)
-- Puesto que el límite de uₙ es a, existe un k ∈ ℕ tal que
--    (∀ n ≥ k)[|uₙ - a| < ε/|c|]                                    (2)
-- Veamos que con k se cumple (1). En efecto, sea n ≥ k. Entonces,
--    |-uₙ - -a| = |-(uₙ - a)|
--               = |uₙ - a|
--               < ε           [por (2)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ -u n) (-a) :=
by
  unfold limite at *
  -- h : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => -u n) n - -a| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => -u n) n - -a| < ε
  specialize h ε hε
  -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  cases' h with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |(fun n => -u n) n - -a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(fun n => -u n) n - -a| < ε
  calc |(fun n => -u n) n - -a|
       = |(-u n - -a)|          := rfl
     _ = |(-(u n - a))|         := by congr ; ring
     _ = |(u n - a)|            := abs_neg (u n - a)
     _ < ε                      := hk n hn

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ -u n) (-a) :=
by
  unfold limite at *
  -- h : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => -u n) n - -a| < ε
  have h1 : ∀ n, |u n - a| = |(-u n - -a)| := by
    intro n
    -- n : ℕ
    -- ⊢ |u n - a| = |-u n - -a|
    rw [abs_sub_comm]
    -- ⊢ |a - u n| = |-u n - -a|
    congr 1
    -- ⊢ a - u n = -u n - -a
    ring
  simpa [h1] using h

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- #check (abs_neg a : |(-a)| = |a|)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
