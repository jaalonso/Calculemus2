-- Limite_de_sucesiones_no_decrecientes.lean
-- Si u es una sucesión no decreciente y su límite es a, entonces u(n) ≤ a para todo n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- En Lean4, se define que a es el límite de la sucesión u, por
--    def limite (u: ℕ → ℝ) (a: ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- y que la sucesión u es no decreciente por
--    def no_decreciente (u : ℕ → ℝ) :=
--      ∀ n m, n ≤ m → u n ≤ u m
--
-- Demostrar que si u es una sucesión no decreciente y su límite es a,
-- entonces u(n) ≤ a para todo n.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostraremos por reducción al absurdo. Para ello, sea n ∈ ℕ tal
-- que
--    a < u(n)
-- Entonces,
--    u(n) - a > 0
-- y, puesto que a es límite de u, existe un m ∈ ℕ tal que
--    (∀ n' ≥ m)[|u(n') - a| < u(n) - a]                             (1)
-- Sea k = máx(n, m). Entonces,
--    k ≥ n                                                          (2)
--    k ≥ m                                                          (3)
-- Por (1) y (3) se tiene que
--    |u(k) - a| < u(n) - a                                          (4)
-- Por (2), puesto que u es no decreciente, se tiene que
--    u(n) ≤ u(k)                                                    (5)
-- Por tanto,
--    u(k) - a ≤ |u(k) - a|
--             < u(n) - a      [por (4)]
--             ≤ u(k) - a      [por (5)]
-- Luego,
--    u(k) - a < u(k) - a
-- que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable (a : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  replace H : u n - a > 0 := sub_pos.mpr H
  cases' h (u n - a) H with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  let k := max n m
  have h1 : k ≥ n := le_max_left n m
  have h2 : k ≥ m := le_max_right n m
  have h3 : u k - a < u k - a := by
    calc u k  - a ≤ |u k - a| := by exact le_abs_self (u k - a)
                _ < u n - a   := hm k h2
                _ ≤ u k - a   := sub_le_sub_right (h' n k h1) a
  exact gt_irrefl (u k - a) h3

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  replace H : u n - a > 0 := sub_pos.mpr H
  cases' h (u n - a) H with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  let k := max n m
  specialize hm k (le_max_right _ _)
  -- hm : |u k - a| < u n - a
  specialize h' n k (le_max_left _ _)
  -- h' : u n ≤ u k
  replace hm : |u k - a| < u k - a := by
    calc |u k - a| < u n - a := by exact hm
                 _ ≤ u k - a := sub_le_sub_right h' a
  rw [← not_le] at hm
  -- hm : ¬u k - a ≤ |u k - a|
  apply hm
  -- ⊢ u k - a ≤ |u k - a|
  exact le_abs_self (u k - a)

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  cases' h (u n - a) (by linarith) with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  specialize hm (max n m) (le_max_right _ _)
  -- hm : |u (max n m) - a| < u n - a
  specialize h' n (max n m) (le_max_left _ _)
  -- h' : u n ≤ u (max n m)
  rw [abs_lt] at hm
  -- hm : -(u n - a) < u (max n m) - a ∧ u (max n m) - a < u n - a
  linarith

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- #check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
-- #check (gt_irrefl a : ¬(a > a))
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
-- #check (sub_pos : 0 < a - b ↔ b < a)
