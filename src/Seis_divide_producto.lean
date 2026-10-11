-- Reto_16.lean
-- Para todo n ∈ N, n(n+1)(2n+1) es divisible por 6.
-- Sevilla, 24-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que, para todo n ∈ N, n(n+1)(2n+1) es divisible
-- por 6.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- 1ª demostración
-- ===============

-- Como 2 y 3 son primos entre sí, para demostrar que
-- n(n+1)(2n+1) es divisible por 6 basta demostrar que lo es
-- por 2 y por 3.
--
-- Para demostrar que n(n+1)(2n+1) es divisible por 2,
-- consideramos dos casos según el resto de dividir n entre
-- 2; es decir, según el valor de n % 2.
--
-- Caso 1: Si n % 2 = 0, entonces n es divible entre 2 y, por
-- tanto, también lo es n(n+1)(2n+1).
--
-- Caso 2: Si n % 2 = 1, entonces n+1 es divible entre 2 y,
-- por tanto, también lo es n(n+1)(2n+1).
--
-- Para demostrar que n(n+1)(2n+1) es divisible por 3,
-- consideramos tres casos según el resto de dividir n entre
-- 3; es decir, según el valor de n % 3.
--
-- Caso 1: Si n % 3 = 0, entonces n es divible entre 3 y, por
-- tanto, también lo es n(n+1)(2n+1)
--
-- Caso 2: Si n % 3 = 1, entonces 2n+1 es divible entre 3 y,
-- por tanto, también lo es n(n+1)(2n+1).
--
-- Caso 3: Si n % 3 = 2, entonces n+1 es divible entre 3 y,
-- por tanto, también lo es n(n+1)(2n+1).

-- 2ª demostración
-- ===============

-- Demostraremos, por inducción en n, que
--    6 ∣ n(n+1)(2n+1)
--
-- Base: Para n = 0, se tiene trivialmente que
--    6 | 0 * (0 + 1) * (2 * 0 + 1)
--
-- Paso de inducción: Supongamos que n verifica la hipótesis
-- de inducción:
--    6 ∣ n(n+1)(2n+1)                                    (HI)
-- Tenemos que demostrar que
--    6 ∣ (n+1)((n+1)+1)(2(n+1)+1)
--
-- Por la HI, existe un k tal que
--    n(n+1)(2n+1) = 6k                                   (1)
--
-- La diferencia es
--    (n+1)((n+1)+1)(2(n+1)+1) - n(n+1)(2n+1)
--    = (n+1)(n+2)(2n+3) - n(n+1)(2n+1)
--    = (n+1)[(n+2)(2n+3) - n(2n+1)]
--    = (n+1)[2n² + 7n + 6 - 2n² - n]
--    = (n+1)(6n + 6)
--    = 6(n+1)²
--
-- Por tanto,
--    (n+1)((n+1)+1)(2(n+1)+1)
--    = n(n+1)(2n+1) + 6(n+1)²
--    = 6k + 6(n+1)²             [por (1)]
--    = 6(k + (n+1)²)
-- que es divisible por 6.

-- 3ª demostración
-- ===============

-- Usando aritmética modular en ℤ₆, demostrar que
--    6 ∣ n * (n + 1) * (2 * n + 1)
-- se reduce a
--    n * (n + 1) * (2 * n + 1) ≡ 0 (mod 6)
-- lo que se verifica trivialmente.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Tactic

variable (n : ℕ)

-- 1ª demostración
-- ===============

example : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  have h1 : Nat.Coprime 2 3 := by norm_num
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h1
  · -- ⊢ 2 ∣ n * (n + 1) * (2 * n + 1)
    have h2 : n % 2 < 2 := by omega
    interval_cases h4 : n % 2
    · -- h4 : n % 2 = 0
      have h5 : 2 ∣ n := by omega
      have h6 : 2 ∣ n * (n + 1) := dvd_mul_of_dvd_left h5 (n + 1)
      exact dvd_mul_of_dvd_left h6 (2 * n + 1)
    · -- h4 : n % 2 = 1
      have h5 : 2 ∣ n + 1 := by omega
      have h6 : 2 ∣ n * (n + 1) := dvd_mul_of_dvd_right h5 n
      exact dvd_mul_of_dvd_left h6 (2 * n + 1)
  · -- ⊢ 3 ∣ n * (n + 1) * (2 * n + 1)
    have h3 : n % 3 < 3 := by omega
    interval_cases h4 : n % 3
    · -- h4 : n % 3 = 0
      have h5 : 3 ∣ n := by omega
      have h6 : 3 ∣ n * (n + 1) := dvd_mul_of_dvd_left h5 (n + 1)
      exact dvd_mul_of_dvd_left h6 (2 * n + 1)
    · -- h4 : n % 3 = 1
      have h5 : 3 ∣ 2 * n + 1 := by omega
      exact dvd_mul_of_dvd_right h5 (n * (n + 1))
    · -- h4 : n % 3 = 2
      have h5 : 3 ∣ n + 1 := by omega
      have h6 : 3 ∣ n * (n + 1) := dvd_mul_of_dvd_right h5 n
      exact dvd_mul_of_dvd_left h6 (2 * n + 1)

-- 2ª demostración
-- ===============

example : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  have h1 : Nat.Coprime 2 3 := by norm_num
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h1
  · -- ⊢ 2 ∣ n * (n + 1) * (2 * n + 1)
    have h2 : n % 2 < 2 := by omega
    interval_cases h4 : n % 2
    · -- h4 : n % 2 = 0
      have h5 : 2 ∣ n := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h5 (n + 1)) (2 * n + 1)
    · -- h4 : n % 2 = 1
      have h5 : 2 ∣ n + 1 := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h5 n) (2 * n + 1)
  · -- ⊢ 3 ∣ n * (n + 1) * (2 * n + 1)
    have h3 : n % 3 < 3 := by omega
    interval_cases h4 : n % 3
    · -- h4 : n % 3 = 0
      have h5 : 3 ∣ n := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h5 (n + 1)) (2 * n + 1)
    · -- h4 : n % 3 = 1
      have h5 : 3 ∣ 2 * n + 1 := by omega
      exact dvd_mul_of_dvd_right h5 (n * (n + 1))
    · -- h4 : n % 3 = 2
      have h5 : 3 ∣ n + 1 := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h5 n) (2 * n + 1)

-- 3ª demostración
-- ===============

example : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero =>
    -- ⊢ 6 ∣ 0 * (0 + 1) * (2 * 0 + 1)
    use 0
  | succ n ih =>
    -- n : ℕ
    -- ih : 6 ∣ n * (n + 1) * (2 * n + 1)
    -- ⊢ 6 ∣ (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
    obtain ⟨k, hk⟩ := ih
    -- k : ℕ
    -- hk : n * (n + 1) * (2 * n + 1) = 6 * k
    exact ⟨k + (n + 1) ^ 2, by linear_combination hk⟩

-- 4ª demostración
-- ===============

example : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero =>
    -- ⊢ 6 ∣ 0 * (0 + 1) * (2 * 0 + 1)
    use 0
  | succ n ih =>
    -- n : ℕ
    -- ih : 6 ∣ n * (n + 1) * (2 * n + 1)
    -- ⊢ 6 ∣ (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
    have h1 : (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1)
              = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by ring
    obtain ⟨k, hk⟩ := ih
    -- k : ℕ
    -- hk : n * (n + 1) * (2 * n + 1) = 6 * k
    use k + (n + 1) ^ 2
    -- ⊢ (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) = 6 * (k +
    -- (n + 1) ^ 2)
    calc (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
       _ = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by ring
       _ = 6 * k + 6 * (n + 1) ^ 2                     := by rw [hk]
       _ = 6 * (k + (n + 1) ^ 2)                       := by grind

-- 5ª demostración
-- ===============

example : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  have h : ∀ k : ZMod 6, k * (k + 1) * (2 * k + 1) = 0 := by decide
  rw [← ZMod.natCast_eq_zero_iff]
  -- ⊢ ↑(n * (n + 1) * (2 * n + 1)) = 0
  push_cast
  -- ⊢ ↑n * (↑n + 1) * (2 * ↑n + 1) = 0
  exact h n
