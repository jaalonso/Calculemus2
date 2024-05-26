-- Acotacion_de_convergentes.lean
-- Las sucesiones convergentes están acotadas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si u es una sucesión convergente, entonces está
-- acotada; es decir,
--     ∃ k b. ∀n≥k. ¦u n¦ ≤ b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que la sucesión uₙ es convergente, existe un a ∈ ℝ tal que
--    lim(uₙ) = a
-- Luego, existe un k ∈ ℕ tal que
--    (∀ n ∈ ℕ)[n ≥ k → |uₙ - a | < 1]                               (1)
-- Veamos que uₙ está acotada por 1 + |a|; es decir,
--    (∀ n ∈ ℕ)[n ≥ k → |uₙ| ≤ 1 + |a]]
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ k.                                                         (2)
-- Entonces,
--    |uₙ| = |uₙ - a + a|
--         ≤ |uₙ - a| + |a|
--         ≤ 1 + |a|          [por (1) y (2)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

-- 1ª demostración
-- ===============

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
by
  cases' h with a ua
  -- a : ℝ
  -- ua : limite u a
  cases' ua 1 zero_lt_one with k h
  -- k : ℕ
  -- h : ∀ (n : ℕ), n ≥ k → |u n - a| ≤ 1
  use k, 1 + |a|
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n| ≤ 1 + |a|
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n| ≤ 1 + |a|
  specialize h n hn
  -- ⊢ |u n| ≤ 1 + |a|
  calc |u n|
       = |u n - a + a|   := congr_arg abs (eq_add_of_sub_eq rfl)
     _ ≤ |u n - a| + |a| := abs_add (u n - a) a
     _ ≤ 1 + |a|         := add_le_add_right h |a|

-- 2ª demostración
-- ===============

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
by
  cases' h with a ua
  -- a : ℝ
  -- ua : limite u a
  cases' ua 1 zero_lt_one with k h
  -- k : ℕ
  -- h : ∀ (n : ℕ), n ≥ k → |u n - a| ≤ 1
  use k, 1 + |a|
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n| ≤ 1 + |a|
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n| ≤ 1 + |a|
  specialize h n hn
  -- h : |u n - a| ≤ 1
  calc |u n|
       = |u n - a + a|   := by ring_nf
     _ ≤ |u n - a| + |a| := abs_add (u n - a) a
     _ ≤ 1 + |a|         := by linarith

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_le_add_right : b ≤ c → ∀ a,  b + a ≤ c + a)
-- #check (eq_add_of_sub_eq :  a - c = b → a = b + c)
-- #check (zero_lt_one : 0 < 1)
