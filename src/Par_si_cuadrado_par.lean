-- Par_si_cuadrado_par.lean
-- Si n² es par, entonces n es par.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si n² es par, entonces n es par.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usara el siguiente lema: "Si p es primo, entonces
--    (∀ a, b ∈ ℕ)[p ∣ ab ↔ p ∣ a ∨ p ∣ b].
--
-- Si n² es par, entonces 2 divide a n.n y, por el lema, 2 divide a n.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Nat

variable (n : ℕ)

-- 1ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h1 : Nat.Prime 2 := prime_two
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Nat.Prime.dvd_mul h1).mp h
  rcases h2 with h3 | h4
  · -- h3 : 2 ∣ n
    exact h3
  · -- h4 : 2 ∣ n
    exact h4

-- 2ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Nat.Prime.dvd_mul prime_two).mp h
  rcases h2 with h3 | h4
  · exact h3
  · exact h4

-- 3ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Nat.Prime.dvd_mul prime_two).mp h
  cases h2 <;> assumption

-- 4ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Nat.Prime.dvd_mul prime_two).mp h
  tauto

-- 5ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  -- h : 2 ∣ n ∨ 2 ∣ n
  -- ⊢ 2 ∣ n
  tauto

-- Lemas usados
-- ============

-- variable (p a b : ℕ)
-- #check (prime_two : Nat.Prime 2)
-- #check (Nat.Prime.dvd_mul : Nat.Prime p → (p ∣ a * b ↔ p ∣ a ∨ p ∣ b))
