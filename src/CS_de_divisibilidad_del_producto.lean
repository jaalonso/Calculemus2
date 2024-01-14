-- CS_de_divisibilidad_del_producto.lean
-- Si m divide a n o a k, entonces m divide a nk.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si m divide a n o a k, entonces m divide a nk.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por casos.
--
-- Caso 1: Supongamos que m ∣ n. Entonces, existe un a ∈ ℕ tal que
--    n = ma
-- Por tanto,
--    nk = (ma)k
--       = m(ak)
-- que es divisible por m.
--
-- Caso 2: Supongamos que m ∣ k. Entonces, existe un b ∈ ℕ tal que
--    k = mb
-- Por tanto,
--    nk = n(mb)
--       = m(nb)
-- que es divisible por m.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable {m n k : ℕ}

-- 1ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    rcases h1 with ⟨a, ha⟩
    -- a : ℕ
    -- ha : n = m * a
    rw [ha]
    -- ⊢ m ∣ (m * a) * k
    rw [mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- h2 : m ∣ k
    rcases h2 with ⟨b, hb⟩
    -- b : ℕ
    -- hb : k = m * b
    rw [hb]
    -- ⊢ m ∣ n * (m * b)
    rw [mul_comm]
    -- ⊢ m ∣ (m * b) * n
    rw [mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 2ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    rcases h1 with ⟨a, ha⟩
    -- a : ℕ
    -- ha : n = m * a
    rw [ha, mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- h2 : m ∣ k
    rcases h2 with ⟨b, hb⟩
    -- b : ℕ
    -- hb : k = m * b
    rw [hb, mul_comm, mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 3ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  . -- a : ℕ
    -- ⊢ m ∣ (m * a) * k
    rw [mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- ⊢ m ∣ n * (m * b)
    rw [mul_comm, mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 4ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    exact dvd_mul_of_dvd_left h1 k
  . -- h2 : m ∣ k
    exact dvd_mul_of_dvd_right h2 n

-- Lemas usados
-- ============

-- #check (dvd_mul_of_dvd_left : m ∣ n → ∀ (c : ℕ), m ∣ n * c)
-- #check (dvd_mul_of_dvd_right : m ∣ n → ∀ (c : ℕ), m ∣ c * n)
-- #check (dvd_mul_right m n : m ∣ m * n)
-- #check (mul_assoc m n k : m * n * k = m * (n * k))
-- #check (mul_comm m n : m * n = n * m)
