-- Reto_5.lean
-- Soluciones de 5º reto (7 de junio de 2026).
-- 5²ⁿ - 2³ⁿ es divisible por 17.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, 5²ⁿ - 2³ⁿ es divisible por 17 para todo número
-- natural n.
-- ---------------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- 1ª demostración en lenguaje natural (LN1)
-- =========================================
--
-- Considerando que
--    5²ⁿ - 2³ⁿ = (5²)ⁿ - (2³)ⁿ
--              = 25ⁿ - 8ⁿ
-- Lo que tenemos que demostrar es que, para todo número natural n,
--    17 | 25ⁿ - 8ⁿ
-- Lo haremos por inducción.
--
-- Caso base (n = 0):
--    25ⁿ - 8ⁿ = 25⁰ - 8⁰
--             = 0
-- que es divisble por 17.
--
-- Paso de inducción: Supongamos que
--    17 | 25ⁿ - 8ⁿ                                                 (HI)
-- y, por tanto, existe un k tal que
--    25ⁿ - 8ⁿ = 17k                                                (1)
-- Tenemos que probar que
--    17 | 25ⁿ⁺¹ - 8ⁿ⁺¹
-- Luego,
--    25ⁿ⁺¹ - 8ⁿ⁺¹ = 25·25ⁿ − 8·8ⁿ
--                 = (17+8)·25ⁿ − 8·8ⁿ
--                 = 17·25ⁿ + 8·25ⁿ − 8·8ⁿ
--                 = 17·25ⁿ + 8·(25ⁿ − 8ⁿ)
--                 = 17·25ⁿ + 8·17k           [por (1)]
--                 = 17·(25ⁿ + 8k)
-- Por tanto,
--    17 | 25ⁿ⁺¹ - 8ⁿ⁺¹
--
-- 2ª demostración en lenguaje natural (LN2)
-- =========================================
--
-- Por indución en n.
--
-- Caso base (n = 0)
--    5⁽²·⁰⁾ - 2⁽³·⁰⁾ = 0
-- que es divisble por 17.
--
-- Paso de inducción: Supongamos que
--    17 | 5²ⁿ - 2³ⁿ
-- y tenemos que probar que
--    17 | 5⁽²ⁿ⁺¹⁾ − 2⁽³ⁿ⁺¹⁾
-- De la HI, se tiene que existe un k tal que
--    5²ⁿ - 2³ⁿ = 17k                                             (1)
-- Luego,
--    5⁽²ⁿ⁺¹⁾ − 2⁽³ⁿ⁺¹⁾ = 5²ⁿ·5² − 2³ⁿ·2³
--                      = (17k + 2³ⁿ)·5^2 − 2³ⁿ · 2^3     [por (1)]
--                      = 17k·25 + 25·2³ⁿ − 8·2³ⁿ
--                      = 17·(25k) + (25 - 8)·2³ⁿ
--                      = 17·(25k + 2³ⁿ)
-- Por tanto,
--    17 | 5⁽²ⁿ⁺¹⁾ − 2⁽³ⁿ⁺¹⁾
--
-- 3ª demostración en lenguaje natural (LN3)
-- =========================================
--
-- Usando aritmética modular
--    5²ⁿ - 2³ⁿ = 25ⁿ − 8ⁿ
--              ≡ 8ⁿ − 8ⁿ (mód 17)
--              ≡ 0 (mód 17)
--
-- 4ª demostración en lenguaje natural (LN4)
-- =========================================
--
-- Se tiene que
--     5²ⁿ - 2³ⁿ = 25ⁿ − 8ⁿ
-- que que es divisible por 25 - 8 (ya que xⁿ - yⁿ es divisible por
-- x - y). Por tanto, 5²ⁿ - 2³ⁿ es divisible por 17.

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

variable (n : ℕ)

open Nat

-- 1ª demostración (basada en la LN1)
-- ==================================

namespace Demostracion1

lemma L1 : (17 * 25^n + 8 * 25^n) - 8 * 8^n =
           17 * 25^n + (8 * 25^n - 8 * 8^n) :=
by
  apply Nat.add_sub_assoc
  -- ⊢ 8 * 8 ^ n ≤ 8 * 25 ^ n
  bound

lemma L2 : 17 ∣ 25^n - 8^n :=
by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 25 ^ 0 - 8 ^ 0
    simp
  | succ n HI =>
    -- n : ℕ
    -- HI : 17 ∣ 25 ^ n - 8 ^ n
    -- ⊢ 17 ∣ 25 ^ (n + 1) - 8 ^ (n + 1)
    obtain ⟨k, hk⟩ := HI
    -- k : ℕ
    -- hk : 25 ^ n - 8 ^ n = 17 * k
    use 25^n + 8*k
    -- ⊢ 25 ^ (n + 1) - 8 ^ (n + 1) = 17 * (25 ^ n + 8 * k)
    calc 25 ^ (n + 1) - 8 ^ (n + 1)
     _ = 25 * 25^n - 8 * 8^n              := by grind
     _ = (17+8) * 25^n - 8 * 8^n          := by grind
     _ = (17 * 25^n + 8 * 25^n) - 8 * 8^n := by grind
     _ = 17 * 25^n + (8 * 25^n - 8 * 8^n) := L1 n
     _ = 17 * 25^n + 8 * (25^n - 8^n)     := by grind
     _ = 17 * 25^n + 8 * 17*k             := by grind
     _ = 17 * (25^n + 8 * k)              := by grind
     _ = 17 * (25 ^ n + 8 * k)            := by grind

example : 17 ∣ 5^(2 * n) - 2^(3 * n) :=
by
  have h1 : 5^(2 * n) - 2^(3 * n) = 25^n - 8^n :=
    by calc 5^(2 * n) - 2^(3 * n)
          = (5^2)^n - (2^3)^n     := by simp only [pow_mul]
        _ = 25^n - 8^n            := by norm_num
  rw [h1]
  -- ⊢ 17 ∣ 25 ^ n - 8 ^ n
  exact L2 n

end Demostracion1

-- 2ª demostración (explicitación de la 1ª)
-- ========================================

namespace Demostracion2

lemma L1 : (17 * 25^n + 8 * 25^n) - 8 * 8^n =
           17 * 25^n + (8 * 25^n - 8 * 8^n) :=
by
  apply Nat.add_sub_assoc
  -- ⊢ 8 * 8 ^ n ≤ 8 * 25 ^ n
  bound

example : 25 ^ (n + 1) = 25^n * 25 := by simp only [Nat.pow_add_one]

lemma L2 : 17 ∣ 25^n - 8^n :=
by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 25 ^ 0 - 8 ^ 0
    simp
  | succ n HI =>
    -- n : ℕ
    -- HI : 17 ∣ 25 ^ n - 8 ^ n
    -- ⊢ 17 ∣ 25 ^ (n + 1) - 8 ^ (n + 1)
    obtain ⟨k, hk⟩ := HI
    -- k : ℕ
    -- hk : 25 ^ n - 8 ^ n = 17 * k
    use 25^n + 8*k
    -- ⊢ 25 ^ (n + 1) - 8 ^ (n + 1) = 17 * (25 ^ n + 8 * k)
    calc 25 ^ (n + 1) - 8 ^ (n + 1)
     _ = 25^n * 25 - 8^n * 8              := by simp only [Nat.pow_add_one]
     _ = 25 * 25^n - 8 * 8^n              := by simp only [mul_comm]
     _ = (17+8) * 25^n - 8 * 8^n          := by norm_num
     _ = (17 * 25^n + 8 * 25^n) - 8 * 8^n := by simp only [right_distrib]
     _ = 17 * 25^n + (8 * 25^n - 8 * 8^n) := L1 n
     _ = 17 * 25^n + 8 * (25^n - 8^n)     := by simp only [Nat.mul_sub]
     _ = 17 * 25^n + 8 * (17 * k)         := by rw [hk]
     _ = 17 * (25^n + 8 * k)              := by simp +arith

example : 17 ∣ 5^(2 * n) - 2^(3 * n) :=
by
  have h1 : 5^(2 * n) - 2^(3 * n) = 25^n - 8^n :=
    by calc 5^(2 * n) - 2^(3 * n)
          = (5^2)^n - (2^3)^n     := by simp only [pow_mul]
        _ = 25^n - 8^n            := by norm_num
  rw [h1]
  -- ⊢ 17 ∣ 25 ^ n - 8 ^ n
  exact L2 n

end Demostracion2

-- 3ª demostración (basada en la LN2)
-- ==================================

namespace Demostracion3

lemma L1 : 2^(3*n) ≤ 5^(2*n) := by
  have h : 2^3 ≤ 5^2 := by norm_num
  calc 2^(3*n)
       = (2^3)^n := pow_mul 2 3 n
     _ ≤ (5^2)^n := Nat.pow_le_pow_left h n
     _ = 5^(2*n) := (pow_mul 5 2 n).symm

example : 17 ∣ 5^(2 * n) - 2^(3 * n) :=
by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 5 ^ (2 * 0) - 2 ^ (3 * 0)
    simp
  | succ n HI =>
    -- n : ℕ
    -- HI : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n)
    -- ⊢ 17 ∣ 5 ^ (2 * (n + 1)) - 2 ^ (3 * (n + 1))
    obtain ⟨k, hk⟩ := HI
    -- k : ℕ
    -- hk : 5^(2*n)-2^(3*n) = 17*k
    use 25 * k + 2 ^ (3 * n)
    -- ⊢ 5^(2*(n+1))-2^(3*(n+1)) = 17*(25*k+2^(3*n))
    calc 5^(2*(n+1))-2^(3*(n+1))
         = 5^(2*n)*5^2-2^(3*n)*2^3         := by grind
       _ = (17*k+2^(3*n))*5^2-2^(3*n)*2^3  := by grind [L1]
       _ = 17*k*25+25*2^(3*n)-8*2^(3*n)    := by grind
       _ = 17*(25*k)+(25-8)*2^(3*n)        := by grind
       _ = 17*(25*k+2^(3*n))               := by grind

end Demostracion3

-- 4ª demostración (explicitación de la 3ª)
-- ========================================

namespace Demostracion4

lemma L1 : 2^(3*n) ≤ 5^(2*n) := by
  have h : 2^3 ≤ 5^2 := by norm_num
  calc 2^(3*n)
       = (2^3)^n := pow_mul 2 3 n
     _ ≤ (5^2)^n := Nat.pow_le_pow_left h n
     _ = 5^(2*n) := (pow_mul 5 2 n).symm

lemma L2
  (hk : 5 ^ (2 * n) - 2 ^ (3 * n) = 17 * k)
  : 5 ^ (2 * n) = 17 * k + 2 ^ (3 * n) :=
(Nat.sub_eq_iff_eq_add (L1 n)).mp hk

example : 17 ∣ 5^(2 * n) - 2^(3 * n) :=
by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 5 ^ (2 * 0) - 2 ^ (3 * 0)
    simp
  | succ n HI =>
    -- n : ℕ
    -- HI : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n)
    -- ⊢ 17 ∣ 5 ^ (2 * (n + 1)) - 2 ^ (3 * (n + 1))
    obtain ⟨k, hk⟩ := HI
    -- k : ℕ
    -- hk : 5^(2*n)-2^(3*n) = 17*k
    use 25 * k + 2 ^ (3 * n)
    -- ⊢ 5^(2*(n+1))-2^(3*(n+1)) = 17*(25*k+2^(3*n))
    calc 5^(2*(n+1))-2^(3*(n+1))
         = 5^(2*n+2)-2^(3*n+3)             := by simp +arith only
       _ = 5^(2*n)*5^2-2^(3*n)*2^3         := by noncomm_ring
       _ = (17*k+2^(3*n))*5^2-2^(3*n)*2^3  := by simp [hk, L2]
       _ = 17*k*25+25*2^(3*n)-8*2^(3*n)    := by omega
       _ = 17*(25*k)+(25-8)*2^(3*n)        := by omega
       _ = 17*(25*k+2^(3*n))               := by ring

end Demostracion4

-- 5ª demostración (basasa en la LN3)
-- ==================================

namespace Demostracion5

example : 17 ∣ 5^(2*n) - 2^(3*n) :=
by
  have h1 : 25 ≡ 8 [MOD 17] := by decide
  apply modEq_zero_iff_dvd.mp
  -- ⊢ 5 ^ (2 * n) - 2 ^ (3 * n) ≡ 0 [MOD 17]
  calc 5^(2*n) - 2^(3*n)
       = 25^n - 8^n         := by simp [pow_mul]
     _ ≡ 8^n - 8^n [MOD 17] := by apply ModEq.sub_right
                                  · -- ⊢ 8 ^ n ≤ 25 ^ n
                                    bound
                                  · -- ⊢ 8 ^ n ≤ 8 ^ n
                                    gcongr
                                  exact (ModEq.pow n h1)
     _ = 0                  := by simp
     _ ≡ 0 [MOD 17]         := ModEq.refl 0

end Demostracion5

-- 6ª demostración (hasada en la LN4)
-- ==================================

namespace Demostracion6

example : 17 ∣ (5 ^ (2 * n) - 2 ^ (3 * n)) :=
by
  rw [pow_mul, pow_mul]
  -- ⊢ 17 ∣ (5 ^ 2) ^ n - (2 ^ 3) ^ n
  exact Nat.sub_dvd_pow_sub_pow 25 8 n

-- Nota: En la demostración anterior la inducción está oculta en
-- [Nat.sub_dvd_pow_sub_pow](https://1pt.co/34pbu) que usa
-- [pow_le_pow_left](https://1pt.co/ydx7a) que se demuestra por
-- inducción.

end Demostracion6

-- 7ª demostración (simplificación de la 6ª)
-- ===============

namespace Demostracion7

example (n : ℕ) : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n) :=
by
  simpa [pow_mul] using Nat.sub_dvd_pow_sub_pow 25 8 n

end Demostracion7

-- 8ª demostración con comentarios
-- ===============================

namespace Demostracion8

example (n : ℕ) : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n) := by
  induction n with
  | zero =>
    -- Caso base: 5^0 - 2^0 = 0, y 17 | 0.
    simp
  | succ k ih =>
    -- 1. Preparar las potencias (usamos 'ring' para manejar la conmutatividad)
    have h_pow5 : 5 ^ (2 * (k + 1)) = 25 * 5 ^ (2 * k) := by
      rw [mul_add, pow_add]
      ring
    have h_pow2 : 2 ^ (3 * (k + 1)) = 8 * 2 ^ (3 * k) := by
      rw [mul_add, pow_add]
      ring
    rw [h_pow5, h_pow2]

    -- 2. Demostrar que 2^(3k) ≤ 5^(2k) para poder operar restas en Nat
    -- (8^k ≤ 25^k)
    have h_le : 2 ^ (3 * k) ≤ 5 ^ (2 * k) := by
      rw [pow_mul, pow_mul]
      -- Nombre corregido: Nat.pow_le_pow_left
      apply Nat.pow_le_pow_left (by norm_num)

    -- 3. Aplicar el truco de "sumar y restar" (Método Hirsch / 1ª Forma)
    -- Descomponemos 25 como (17 + 8)
    have h_split : 25 * 5 ^ (2 * k) = 17 * 5 ^ (2 * k) + 8 * 5 ^ (2 * k) := by ring
    rw [h_split]

    -- Asociamos los términos: 17*5^(2k) + (8*5^(2k) - 8*2^(3k))
    -- Nat.add_sub_assoc requiere demostrar que el sustraendo es menor o igual
    rw [Nat.add_sub_assoc (mul_le_mul_left 8 h_le)]

    -- 4. Demostrar divisibilidad por partes
    apply dvd_add
    · -- Caso: 17 ∣ 17 * ...
      apply dvd_mul_right
    · -- Caso: 17 ∣ 8 * (5^(2k) - 2^(3k))
      rw [← Nat.mul_sub_left_distrib]
      apply dvd_mul_of_dvd_right ih

end Demostracion8

-- 9ª demostración (factorización de la 8ª)
-- ========================================

namespace Demostracion9

example : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n) := by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 5 ^ (2 * 0) - 2 ^ (3 * 0)
    simp
  | succ k ih =>
    -- k : ℕ
    -- ih : 17 ∣ 5 ^ (2 * k) - 2 ^ (3 * k)
    -- ⊢ 17 ∣ 5 ^ (2 * (k + 1)) - 2 ^ (3 * (k + 1))
    have h_le : 2 ^ (3 * k) ≤ 5 ^ (2 * k) := by
      calc 2 ^ (3 * k)
           = (2 ^ 3) ^ k := pow_mul 2 3 k
        _  = 8 ^ k       := add_zero (NatPow.pow (2 ^ 3) k)
        _  ≤ 25 ^ k      := Nat.pow_le_pow_left (by norm_num) k
        _  = 5 ^ (2 * k) := (pow_mul 5 2 k).symm
    have h1 : 5 ^ (2 * (k + 1)) - 2 ^ (3 * (k + 1)) =
              17 * 5 ^ (2 * k) + 8 * (5 ^ (2 * k) - 2 ^ (3 * k)) :=
         calc 5 ^ (2 * (k + 1)) - 2 ^ (3 * (k + 1))
              = 25 * 5 ^ (2 * k) - 8 * 2 ^ (3 * k) :=
                  by ring_nf
            _ = 17 * 5 ^ (2 * k) + 8 * (5 ^ (2 * k) - 2 ^ (3 * k)) :=
                  by grind
    rw [h1]
    -- ⊢ 17 ∣ 17 * 5 ^ (2 * k) + 8 * (5 ^ (2 * k) - 2 ^ (3 * k))
    exact dvd_add (dvd_mul_right 17 _) (dvd_mul_of_dvd_right ih 8)

end Demostracion9

-- 10ª demostración
-- ================

namespace Demostracion10

variable (k : ℕ)

lemma L1 : 2 ^ (3 * k) ≤ 5 ^ (2 * k) := by
  rw [pow_mul, pow_mul]
  -- ⊢ (2 ^ 3) ^ k ≤ (5 ^ 2) ^ k
  gcongr 1
  -- ⊢ 2 ^ 3 ≤ 5 ^ 2
  norm_num

lemma L2 :
    5 ^ (2 * (k + 1)) - 2 ^ (3 * (k + 1)) =
    17 * 5 ^ (2 * k) + 8 * (5 ^ (2 * k) - 2 ^ (3 * k)) :=
by
  zify [L1 k, L1 (k + 1)]
  -- ⊢ 5^(2*(k+1))-2^(3*(k+1)) = 17*5^(2*k)+8*(5^(2*k)-2^(3*k))
  ring

example : 17 ∣ 5 ^ (2 * n) - 2 ^ (3 * n) := by
  induction n with
  | zero =>
    -- ⊢ 17 ∣ 5 ^ (2 * 0) - 2 ^ (3 * 0)
    simp
  | succ k ih =>
    -- n k k : ℕ
    -- ih : 17 ∣ 5 ^ (2 * k) - 2 ^ (3 * k)
    -- ⊢ 17 ∣ 5 ^ (2 * (k + 1)) - 2 ^ (3 * (k + 1))
    rw [L2 k]
    -- ⊢ 17 ∣ 17*5^(2*k)+8*(5^(2*k)-2^(3*k))
    exact Dvd.dvd.add (Dvd.intro _ rfl) (Dvd.dvd.mul_left ih 8)

end Demostracion10

-- Lemas usados
-- ============

variable (a b c m k : ℕ)
#check (Dvd.dvd.add : m ∣ n → m ∣ k → m ∣ n + k)
#check (Dvd.dvd.mul_left : m ∣ n → ∀ k, m ∣ k * n)
#check (Dvd.intro k : m * k = n → m ∣ n)
#check (ModEq.pow m : a ≡ b [MOD n] → a ^ m ≡ b ^ m [MOD n])
#check (ModEq.refl a : a ≡ a [MOD n])
#check (ModEq.sub_right : a ≤ b → a ≤ c → b ≡ c [MOD n] → b - a ≡ c - a [MOD n])
#check (Nat.add_sub_assoc : k ≤ m → ∀ n, n + m - k = n + (m - k))
#check (Nat.mul_sub n m k : n * (m - k) = n * m - n * k)
#check (Nat.mul_sub_left_distrib n m k : n * (m - k) = n * m - n * k)
#check (Nat.pow_add_one n m : n ^ (m + 1) = n ^ m * n)
#check (Nat.pow_le_pow_left : n ≤ m → ∀ k, n ^ k ≤ m ^ k)
#check (Nat.sub_dvd_pow_sub_pow m k n : m - k ∣ m ^ n - k ^ n)
#check (Nat.sub_eq_iff_eq_add : b ≤ a → (a - b = c ↔ a = c + b))
#check (add_zero a : a + 0 = a)
#check (dvd_add : m ∣ n → m ∣ k → m ∣ n + k)
#check (dvd_mul_of_dvd_right : m ∣ n → ∀ k, m ∣ k * n)
#check (dvd_mul_right m n : m ∣ m * n)
#check (modEq_zero_iff_dvd : m ≡ 0 [MOD n] ↔ n ∣ m)
#check (mul_add a b c : a * (b + c) = a * b + a * c)
#check (mul_comm n m : n * m = m * n)
#check (mul_le_mul_left k : n ≤ m → k * n ≤ k * m)
#check (pow_add a m n : a ^ (m + n) = a ^ m * a ^ n)
#check (pow_mul m n k : m ^ (n * k) = (m ^ n) ^ k)
#check (right_distrib n m k : (n + m) * k = n * k + m * k)
