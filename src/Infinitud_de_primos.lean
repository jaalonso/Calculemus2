-- Infinitud_de_primos.lean
-- Existen infinitos números primos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que hay infinitos números primos.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas de los números naturales
--    n ≠ 1 → el menor factor primo de n es primo                    (L1)
--    n! > 0                                                         (L2)
--    0 < k → n < k + n                                              (L3)
--    k < n → n ≠ k                                                  (L4)
--    k ≱ n → k ≤ n                                                  (L5)
--    0 < k → k ≤ n → k ∣ n!                                         (L6)
--    0 < minFac(n)                                                  (L7)
--    k ∣ m → (k ∣ n ↔ k ∣ m + n)                                    (L8)
--    minFac(n) ∣ n                                                  (L9)
--    Prime(n) → ¬n ∣ 1                                              (L10)
--
-- Sea p el menor factor primo de n! + 1. Tenemos que demostrar que n ≤
-- p y que p es primo.
--
-- Para demostrar que p es primo, por el lema L1, basta demostrar que
--    n! + 1 ≠ 1
-- Su demostración es
--    n ! > 0           [por L2]
--    ==> n ! + 1 > 1   [por L3]
--    ==> n ! + 1 ≠ 1   [por L4]
--
-- Para demostrar n ≤ p, por el lema L5, basta demostrar que
--    n ≱ p
-- Su demostración es
--    n ≥ p
--    ==> p ∣ n!    [por L6 y L7]
--    ==> p | 1     [por L8 y (p | n! + 1) por L9]
--    ==> Falso     [por L10 y p es primo]

-- Demostración con Lean4
-- ======================

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs

open Nat

-- 1ª demostración
-- ===============

example
  (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p :=
by
  let p := minFac (n !  + 1)
  have h1 : Nat.Prime p := by
    apply minFac_prime
    -- ⊢ n ! + 1 ≠ 1
    have h3 : n ! > 0     := factorial_pos n
    have h4 : n ! + 1 > 1 := Nat.lt_add_of_pos_left h3
    show n ! + 1 ≠ 1
    exact Nat.ne_of_gt h4
  use p
  constructor
  . -- ⊢ n ≤ p
    apply le_of_not_ge
    -- ⊢ ¬n ≥ p
    intro h5
    -- h5 : n ≥ p
    -- ⊢ False
    have h6 : p ∣ n ! := dvd_factorial (minFac_pos _) h5
    have h7 : p ∣ 1   := (Nat.dvd_add_iff_right h6).mpr (minFac_dvd _)
    show False
    exact (Nat.Prime.not_dvd_one h1) h7
  . -- ⊢ Nat.Prime p
    exact h1

-- 2ª demostración
-- ===============

example
  (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p :=
exists_infinite_primes n

-- Lemas usados
-- ============

-- variable (k m n : ℕ)
-- #check (Nat.Prime.not_dvd_one : Nat.Prime n → ¬n ∣ 1)
-- #check (Nat.dvd_add_iff_right : k ∣ m → (k ∣ n ↔ k ∣ m + n))
-- #check (Nat.dvd_one : n ∣ 1 ↔ n = 1)
-- #check (Nat.lt_add_of_pos_left : 0 < k → n < k + n)
-- #check (Nat.ne_of_gt : k < n → n ≠ k)
-- #check (dvd_factorial : 0 < k → k ≤ n → k ∣ n !)
-- #check (factorial_pos n: n ! > 0)
-- #check (le_of_not_ge : ¬k ≥ n → k ≤ n)
-- #check (minFac_dvd n : minFac n ∣ n)
-- #check (minFac_pos n : 0 < minFac n)
-- #check (minFac_prime : n ≠ 1 → Nat.Prime (minFac n))
