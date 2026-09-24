-- Reto_14.lean
-- Para todo n ∈ ℕ, 2n + 9 ≤ 2ⁿ⁺⁴.
-- Sevilla, 9-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que para todo n ∈ ℕ,
--    2n + 9 ≤ 2ⁿ⁺⁴.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en n.
--
-- Caso base: Para n = 0 se tiene:
--    2·0 + 9 = 9
--            ≤ 16
--            = 2⁰⁺⁴
--
-- Paso inductivo: Suponiendo la hipótesis de inducción
--   2k + 9 ≤ 2ᵏ⁺⁴                                        (HI)
-- tenemos que demostrar que
--   2(k+1) + 9 < 2⁽ᵏ⁺¹⁾⁺⁴
--
-- Puesto que k ≥ 0, se tiene que
--   2 ≤ 2ᵏ⁺⁴                                              (1)
-- Efectivamente,
--    2 ≤ 16
--      = 2⁴
--      ≤ 2ᵏ⁺⁴
--
-- Finalmente,
--    2(k + 1) + 9 = (2k + 9) + 2
--                 ≤ 2ᵏ⁺⁴ + 2              [por HI]
--                 ≤ 2ᵏ⁺⁴ + 2ᵏ⁺⁴           [por (1)]
--                 = 2 · 2ᵏ⁺⁴
--                 = 2⁽ᵏ⁺¹⁾⁺⁴

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Tactic

variable (n : ℕ)

-- 1ª demostración
-- ===============

example : 2 * n + 9 ≤ 2 ^ (n + 4) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * 0 + 9 ≤ 2 ^ (0 + 4)
    grind
  | succ k HI =>
    -- k : ℕ
    -- HI : 2 * k + 9 ≤ 2 ^ (k + 4)
    -- ⊢ 2 * (k + 1) + 9 ≤ 2 ^ (k + 1 + 4)
    grind

-- 2ª demostración
-- ===============

example : 2 * n + 9 ≤ 2 ^ (n + 4) :=
by
  induction n <;> grind

-- 3ª demostración
-- ===============

example : 2 * n + 9 ≤ 2 ^ (n + 4) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * 0 + 9 ≤ 2 ^ (0 + 4)
    grind
  | succ k HI =>
    -- k : ℕ
    -- HI : 2 * k + 9 ≤ 2 ^ (k + 4)
    -- ⊢ 2 * (k + 1) + 9 ≤ 2 ^ (k + 1 + 4)
    calc 2 * (k + 1) + 9
         = (2 * k + 9) + 2           := by grind
    _    ≤ 2 ^ (k + 4) + 2           := by grind
    _    ≤ 2 ^ (k + 4) + 2 ^ (k + 4) := by grind
    _    = 2 * 2 ^ (k + 4)           := by grind
    _    = 2 ^ (k + 1 + 4)           := by grind

-- 4ª demostración
-- ===============

example : 2 * n + 9 ≤ 2 ^ (n + 4) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * 0 + 9 ≤ 2 ^ (0 + 4)
    norm_num
  | succ k HI =>
    -- k : ℕ
    -- HI : 2 * k + 9 ≤ 2 ^ (k + 4)
    -- ⊢ 2 * (k + 1) + 9 ≤ 2 ^ (k + 1 + 4)
    calc 2 * (k + 1) + 9
         = (2 * k + 9) + 2           := by ring
    _    ≤ 2 ^ (k + 4) + 2           := Nat.add_le_add_right HI 2
    _    ≤ 2 ^ (k + 4) + 2 ^ (k + 4) := Nat.add_le_add_left (by bound) (2 ^ (k + 4))
    _    = 2 * 2 ^ (k + 4)           := by ring
    _    = 2 ^ (k + 1 + 4)           := by ring

-- 5ª demostración
-- ===============

example : 2 * n + 9 ≤ 2 ^ (n + 4) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * 0 + 9 ≤ 2 ^ (0 + 4)
    calc 2 * 0 + 9
         = 9           := by norm_num
    _    ≤ 16          := by norm_num
    _    = 2 ^ (0 + 4) := by norm_num
  | succ k HI =>
    -- k : ℕ
    -- HI : 2 * k + 9 ≤ 2 ^ (k + 4)
    -- ⊢ 2 * (k + 1) + 9 ≤ 2 ^ (k + 1 + 4)
    have h1 : 2 ≤ 2 ^ (k + 4) := by
      calc 2
           ≤ 16          := by norm_num
      _    = 2 ^ 4       := by norm_num
      _    ≤ 2 ^ (k + 4) := Nat.pow_le_pow_of_le one_lt_two (Nat.le_add_left 4 k)
    calc 2 * (k + 1) + 9
         = (2 * k + 2) + 9           := congrArg (· + 9) (Nat.mul_succ 2 k)
    _    = (2 * k + 9) + 2           := Nat.add_right_comm (2 * k) 2 9
    _    ≤ 2 ^ (k + 4) + 2           := Nat.add_le_add_right HI 2
    _    ≤ 2 ^ (k + 4) + 2 ^ (k + 4) := Nat.add_le_add_left h1 (2 ^ (k + 4))
    _    = 2 * 2 ^ (k + 4)           := (Nat.two_mul (2 ^ (k + 4))).symm
    _    = 2 ^ (k + 1 + 4)           := Nat.pow_succ'.symm


-- Lemas usados
-- ============

variable (k m : ℕ)
#check (Nat.add_le_add_left : n ≤ m → ∀ k, k + n ≤ k + m)
#check (Nat.add_le_add_right : n ≤ m → ∀ k, n + k ≤ m + k)
#check (Nat.add_left_inj : m + n = k + n ↔ m = k)
#check (Nat.le_add_left n m : n ≤ m + n)
#check (Nat.pow_succ' : m ^ n.succ = m * m ^ n)
#check (Nat.two_mul n : 2 * n = n + n)
#check (one_le_two : 1 ≤ 2)
#check (pow_le_pow_right'  : 1 ≤ k → n ≤ m → k ^ n ≤ k ^ m)
