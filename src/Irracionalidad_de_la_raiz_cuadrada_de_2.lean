-- Irracionalidad_de_la_raiz_cuadrada_de_2.lean
-- La raíz cuadrada de 2 es irracional.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la raíz cuadrada de 2 es irracional; es decir, que no
-- existen m, n ∈ ℕ tales que m y n son coprimos (es decir, que no
-- factores comunes distintos de uno) y m² = 2n².
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el lema del ejercicio anterior:
--    (∀ n ∈ ℕ)[2 ∣ n² → 2 | n]
--
-- Supongamos que existen existen m, n ∈ ℕ tales que m y n son coprimos y
-- m² = 2n² y tenemos que demostrar una contradicción. Puesto que 2 no
-- divide a 1, para tener la contradicción basta demostrar que 2 divide
-- a 1 y (puesto que m y n son coprimos), para ello es suficiente
-- demostrar que 2 divide al máximo común divisor de m y n. En
-- definitiva, basta demostrar que 2 divide a m y a n.
--
-- La demostración de que 2 divide a m es
--    m² = 2n² ⟹ 2 | m²
--             ⟹ 2 | m    [por el lema]
--
-- Para demostrar que 2 divide a n, observamos que, puesto que 2 divide
-- a m, existe un k ∈ ℕ tal que m = 2k. Sustituyendo en
--    m² = 2n²
-- se tiene
--    (2k)² = 2n²
-- Simplificando, queda
--    2k = n²
-- Por tanto, 2 divide a n² y, por el lema, 2 divide a n.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs

open Nat
variable {m n : ℕ}

lemma par_si_cuadrado_par
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Nat.Prime.dvd_mul prime_two).mp h
  tauto

example : ¬∃ m n, Coprime m n ∧ m ^ 2 = 2 * n ^ 2 :=
by
  rintro ⟨m, n, ⟨h1, h2⟩⟩
  -- m n : ℕ
  -- h1 : coprime m n
  -- h2 : m ^ 2 = 2 * n ^ 2
  -- ⊢ False
  have h3 : ¬(2 ∣ 1) := by norm_num
  have h4 : 2 ∣ 1 := by
    have h5 : Nat.gcd m n = 1 := h1
    rw [← h5]
    -- ⊢ 2 ∣ Nat.gcd m n
    have h6 : 2 ∣ m := by
      apply par_si_cuadrado_par
      -- ⊢ 2 ∣ m ^ 2
      rw [h2]
      -- ⊢ 2 ∣ 2 * n ^ 2
      exact Nat.dvd_mul_right 2 (n ^ 2)
    have h7 : 2 ∣ n := by
      have h8 : ∃ k, m = 2 * k := h6
      rcases h8 with ⟨k, h9⟩
      -- k : ℕ
      -- h9 : m = 2 * k
      have h10 : 2 * k ^ 2 = n ^ 2 := by
        have h10a : 2 * (2 * k ^ 2) = 2 * n ^ 2 := calc
          2 * (2 * k ^ 2) = (2 * k) ^ 2 := by nlinarith
                        _ = m ^ 2       := by rw [← h9]
                        _ = 2 * n ^ 2   := h2
        show 2 * k ^ 2 = n ^ 2
        exact (mul_right_inj' (by norm_num : 2 ≠ 0)).mp h10a
      have h11 : 2 ∣ n ^ 2 := by
        rw [← h10]
        -- ⊢ 2 ∣ 2 * k ^ 2
        exact Nat.dvd_mul_right 2 (k ^ 2)
      show 2 ∣ n
      exact par_si_cuadrado_par h11
    show 2 ∣ Nat.gcd m n
    exact Nat.dvd_gcd h6 h7
  show False
  exact h3 h4

-- Lemas usados
-- ============

-- variable (p k : ℕ)
-- #check (pow_two n : n ^ 2 = n * n)
-- #check (Prime.dvd_mul : Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣ n))
-- #check (prime_two : Nat.Prime 2)
-- #check (Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n)
-- #check (Nat.dvd_mul_right m n :  m ∣ m * n)
-- #check (mul_right_inj' : k ≠ 0 → (k * m = k * n ↔ m = n))
