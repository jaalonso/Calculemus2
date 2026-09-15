-- Reto_4.lean
-- Soluciones de 4º reto (31 de mayo de 2026).
-- Existen infinitos números primos.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que hay infinitos números primos.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea p el menor factor primo de n! + 1. Tenemos que demostrar que
-- n ≤ p y que p es primo.
--
-- Para demostrar que p es primo, por el lema minFac_prime, basta
-- demostrar que
--    n! + 1 ≠ 1
-- Su demostración es
--    n ! > 0
--    ==> n ! + 1 > 1
--    ==> n ! + 1 ≠ 1
--
-- Para demostrar n ≤ p basta demostrar que
--    n ≱ p
-- Su demostración es
--    n ≥ p
--    ==> p ∣ n!
--    ==> p | 1     [porque p | n! + 1]
--    ==> Falso     [porque p es primo]

-- Demostración con Lean4
-- ======================

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs

open Nat

-- 1ª demostración
-- ===============

example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  set p := minFac (n !  + 1)
  have h1 : Nat.Prime p := by
    apply minFac_prime
    -- ⊢ n ! + 1 ≠ 1
    have h3 : n ! > 0     := factorial_pos n
    have h4 : n ! + 1 > 1 := Nat.lt_add_of_pos_left h3
    exact Nat.ne_of_gt h4
  use p
  -- ⊢ n ≤ p ∧ Nat.Prime p
  constructor
  . -- ⊢ n ≤ p
    apply le_of_not_ge
    -- ⊢ ¬n ≥ p
    intro h5
    -- h5 : n ≥ p
    -- ⊢ False
    have h6 : p ∣ n ! := dvd_factorial (minFac_pos _) h5
    have h7 : p ∣ 1   := (Nat.dvd_add_iff_right h6).mpr (minFac_dvd _)
    exact (Nat.Prime.not_dvd_one h1) h7
  . -- ⊢ Nat.Prime p
    exact h1

-- 2ª demostración
-- ===============

lemma L1 (n : ℕ) : n ! + 1 ≠ 1 :=
  Nat.ne_of_gt (succ_lt_succ (factorial_pos n))

lemma L2 (n : ℕ) : Nat.Prime (minFac (n ! + 1)) :=
  minFac_prime (L1 n)

lemma L3 (n : ℕ) : n ≤ minFac (n ! + 1) :=
by
  by_contra h1
  -- h1 : ¬n ≤ minFac (n ! + 1)
  -- ⊢ False
  apply Nat.Prime.not_dvd_one (L2 n)
  -- ⊢ (n ! + 1).minFac ∣ 1
  have h2 : minFac (n ! + 1) ∣ n ! :=
    dvd_factorial (minFac_pos _) (le_of_not_ge h1)
  exact (Nat.dvd_add_iff_right h2).mpr (minFac_dvd _)

example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
by
  use minFac (n ! + 1)
  -- ⊢ n ≤ (n ! + 1).minFac ∧ Nat.Prime (n ! + 1).minFac
  exact ⟨L3 n, L2 n⟩

-- 3ª demostración
-- ===============

example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
exists_infinite_primes n

-- Lemas usados
-- ============

variable (k m n : ℕ)
#check (Nat.Prime.not_dvd_one : Nat.Prime n → ¬n ∣ 1)
#check (Nat.dvd_add_iff_right : k ∣ m → (k ∣ n ↔ k ∣ m + n))
#check (Nat.lt_add_of_pos_left : 0 < k → n < k + n)
#check (Nat.ne_of_gt : k < n → n ≠ k)
#check (dvd_factorial : 0 < k → k ≤ n → k ∣ n !)
#check (exists_infinite_primes n : ∃ p, n ≤ p ∧ Nat.Prime p)
#check (factorial_pos n: n ! > 0)
#check (le_of_not_ge : ¬k ≥ n → k ≤ n)
#check (minFac_dvd n : minFac n ∣ n)
#check (minFac_pos n : 0 < minFac n)
#check (minFac_prime : n ≠ 1 → Nat.Prime (minFac n))
#check (succ_lt_succ : n < m → n + 1 < m + 1)
