-- Convergencia_de_la_sucesion_1_div_n.lean
-- La sucesión aₙ = 1/n converge a 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-mayo-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una sucesión tal que para todo n, a(n) = 1/n,
-- entonces a converge a 0.
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  sorry
