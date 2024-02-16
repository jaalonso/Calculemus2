-- Limite_cuando_se_suma_una_constante.lean
-- Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de uₙ+c es a+c
-- José A. Alonso Jiménez
-- Sevilla, 12 de febrero de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces
-- el límite de uₙ+c es a+c.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que
--    (∃ N)(∀ n ≥ N)[|(u(n) + c) - (a + c)| < ε]                     (1)
-- Puesto que el límite de la sucesión u(i) es a, existe un k tal que
--    (∀ n ≥ k)[|u(n) - a| < ε]                                      (2)
-- Veamos que con k se verifica (1); es decir, que
--    (∀ n ≥ k)[|(u(n) + c) - (a + c)| < ε]
-- Sea n ≥ k. Entonces, por (2),
--    |u(n) - a| < ε                                                 (3)
-- y, por consiguiente,
--    |(u(n) + c) - (a + c)| = |u(n) - a|
--                           < ε            [por (3)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable {u : ℕ → ℝ}
variable {a c : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i + c) n - (a + c)| < ε
  dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n + c - (a + c)| < ε
  cases' h ε hε with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n + c - (a + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  calc |u n + c - (a + c)|
       = |u n - a|         := by norm_num
     _ < ε                 := hk n hn

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i + c) n - (a + c)| < ε
  dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n + c - (a + c)| < ε
  cases' h ε hε with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n + c - (a + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n + c - (a + c)| < ε
  convert hk n hn using 2
  -- ⊢ u n + c - (a + c) = u n - a
  ring

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  dsimp
  convert h ε hε using 6
  ring

-- 4ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
  fun ε hε ↦ (by convert h ε hε using 6; ring)
