-- Convergencia_de_la_sucesion_constante.lean
-- La sucesión constante sₙ = c converge a c
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, para todo a ∈ ℝ, la sucesión constante
--    s(n) = a
-- converge a a.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada ε ∈ ℝ tal que ε > 0, existe un
-- N ∈ ℕ, tal que (∀n ∈ ℕ)[n ≥ N → |s(n) - a| < ε]. Basta tomar N como
-- 0, ya que para todo n ≥ N se tiene
--    |s(n) - a| = |a - a|
--               = |0|
--               = 0
--               < ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- 1ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun _ => c) n - c| < ε
  intros n _hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |(fun _ => c) n - c| < ε
  show |(fun _ => c) n - c| < ε
  calc |(fun _ => c) n - c| = |c - c| := by dsimp
                          _ = |0|     := by {congr ; exact sub_self c}
                          _ = 0       := abs_zero
                          _ < ε       := hε

-- 2ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun _ => c) n - c| < ε
  intros n _hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |(fun _ => c) n - c| < ε
  show |(fun _ => c) n - c| < ε
  calc |(fun _ => c) n - c| = 0       := by simp
                          _ < ε       := hε

-- 3ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  aesop

-- 4ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  aesop

-- 5ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
  fun ε hε ↦ by aesop

-- Lemas usados
-- ============

-- #check (sub_self a : a - a = 0)
