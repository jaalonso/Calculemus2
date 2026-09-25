-- Reto_15.lean
-- (∃ k ∈ ℕ)(∀ n ∈ ℕ)[(n + k)² ≤ 2ⁿ⁺ᵏ]
-- Sevilla, 18-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que
--    (∃ k ∈ ℕ)(∀ n ∈ N)[(n + k)² ≤ 2ⁿ⁺ᵏ]
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- 1ª demostración
-- ===============

-- En primer lugar demostraremos el siguiente lema auxiliar:
-- Para todo m ≥ 4, se tiene m² ≤ 2ᵐ. Sea m ∈ ℕ, tenemos que
-- demostrar que
--    m ≥ 4 → m ^ 2 ≤ 2 ^ m
-- lo demostraremos por inducción en m.
--
-- Caso base: Para m = 0 se tiene, trivialmente que
--    0 ≥ 4 → 0 ^ 2 ≤ 2 ^ 0
--
-- Paso de inducción: Sea n ∈ ℕ que cumple la hipótesis de
-- inducción; es decir,
--    n ≥ 4 → n ^ 2 ≤ 2 ^ n                               (HI)
-- y tenemos que demostrar que
--    n + 1 ≥ 4 → (n + 1) ^ 2 ≤ 2 ^ (n + 1)
-- Suponiendo que
--    n + 1 ≥ 4                                            (1)
-- tenemos que demostrar que
--    (n + 1) ^ 2 ≤ 2 ^ (n + 1)
-- Lo haremmos por caso según (4 ≤ n).
--
-- Primer caso: Supongamos que
--    4 ≤ n                                                (2)
-- Entonces, demostramos que
--    2 * n + 1 ≤ n ^ 2                                    (3)
-- Efectivamente,
--    2 * n + 1 ≤ 2 * n + 8
--              ≤ 2 * n + 2 * n   [por (2)]
--              = 4 * n
--              ≤ n * n           [por (2)]
--              = n ^ 2
-- Por tanto,
--    (n + 1) ^ 2 = n ^ 2 + 2 * n + 1
--                ≤ n ^ 2 + n ^ 2       [por (3)]
--                = 2 * n ^ 2
--                ≤ 2 * 2 ^ n           [por HI y (2)]
--                = 2 ^ (n + 1)
--
-- Segundo caso: Supongamos que
--    ¬(4 ≤ n)
-- Entonces, por (1), se tiene que
--    n = 3
-- y
--    (n + 1) ^ 2 = (3 + 1) ^ 2
--                = 16
--                ≤ 2 ^ (3 + 1)
--                = 2 ^ (n + 1)
--
-- Para concluir la demostración del ejercicio
--    ∃ k, ∀ n, (n + k) ^ 2 ≤ 2 ^ (n + k)
-- basta usar 4 como k y queda
--    ∀ n, (n + 4) ^ 2 ≤ 2 ^ (n + 4)
-- que se demuestra con el lema auxiliar. En efecto,
-- sea n ∈ ℕ. Entonces,
--    n + 4 ≥ 4
-- y, por el lema auxiliar,
--    (n + 4) ^ 2 ≤ 2 ^ (n + 4).

-- 2ª demostración
-- ===============

-- En primer lugar demostraremos el siguiente lema auxiliar:
-- Para todo m ≥ 4, se tiene m² ≤ 2ᵐ. Sea m ∈ ℕ tal que
--    m ≥ 4
-- tenemos que demostrar que
--    m ^ 2 ≤ 2 ^ m
-- lo demostraremos por inducción generalizada en m a partir
-- de 4.
--
-- Caso base: Para m = 4 se tiene, trivialmente que
--    4 ^ 2 ≤ 2 ^ 4
--
-- Paso de inducción: Sea n ∈ ℕ tal que
--    4 ≤ n                                                (1)
-- y que cumple la hipótesis de inducción; es decir,
--    n ^ 2 ≤ 2 ^ n                                       (HI)
-- y tenemos que demostrar que
--    (n + 1) ^ 2 ≤ 2 ^ (n + 1)
-- Antes, demostramos que
--    2 * n + 1 ≤ n ^ 2                                    (2)
-- Efectivamente,
--    2 * n + 1 ≤ 2 * n + 8
--              ≤ 2 * n + 2 * n   [por (1)]
--              = 4 * n
--              ≤ n * n           [por (1)]
--              = n ^ 2
-- Por tanto,
--    (n + 1) ^ 2 = n ^ 2 + 2 * n + 1
--                ≤ n ^ 2 + n ^ 2       [por (2)]
--                = 2 * n ^ 2
--                ≤ 2 * 2 ^ n           [por HI]
--                = 2 ^ (n + 1)
--
-- Para concluir la demostración del ejercicio
--    ∃ k, ∀ n, (n + k) ^ 2 ≤ 2 ^ (n + k)
-- basta usar 4 como k y queda
--    ∀ n, (n + 4) ^ 2 ≤ 2 ^ (n + 4)
-- que se demuestra con el lema auxiliar. En efecto,
-- sea n ∈ ℕ. Entonces,
--    n + 4 ≥ 4
-- y, por el lema auxiliar,
--    (n + 4) ^ 2 ≤ 2 ^ (n + 4).

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Tactic

-- 1ª solución
-- ===========

namespace Solucion1

lemma aux : ∀ m ≥ 4, m ^ 2 ≤ 2 ^ m := by
  intro m
  -- m : ℕ
  -- ⊢ m ≥ 4 → m ^ 2 ≤ 2 ^ m
  induction m with
  | zero =>
    -- ⊢ 0 ≥ 4 → 0 ^ 2 ≤ 2 ^ 0
    grind
  | succ n hi =>
    -- n : ℕ
    -- hi : n ≥ 4 → n ^ 2 ≤ 2 ^ n
    -- ⊢ n + 1 ≥ 4 → (n + 1) ^ 2 ≤ 2 ^ (n + 1)
    intro hn1
    -- hn1 : n + 1 ≥ 4
    by_cases hn : 4 ≤ n
    · -- hn : 4 ≤ n
      have h1 : 2 * n + 1 ≤ n ^ 2 := by
        calc 2 * n + 1
             ≤ 2 * n + 8     := by grind
        _    ≤ 2 * n + 2 * n := by grind
        _    = 4 * n         := by grind
        _    ≤ n * n         := by gcongr
        _    = n ^ 2         := by grind
      calc (n + 1) ^ 2
           = n ^ 2 + 2 * n + 1 := by grind
      _    ≤ n ^ 2 + n ^ 2     := Nat.add_le_add_left h1 (n ^ 2)
      _    = 2 * n ^ 2         := by grind
      _    ≤ 2 * 2 ^ n         := Nat.mul_le_mul_left 2 (hi hn)
      _    = 2 ^ (n + 1)       := by ring
    · -- hn : ¬4 ≤ n
      have hn3 : n = 3 := by grind
      subst hn3
      -- ⊢ (3 + 1) ^ 2 ≤ 2 ^ (3 + 1)
      norm_num

example : ∃ k : ℕ, ∀ n : ℕ, (n + k) ^ 2 ≤ 2 ^ (n + k) := by
  use 4
  -- ⊢ ∀ (n : ℕ), (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  intro n
  -- ⊢ (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  exact aux (n + 4) (by grind)

end Solucion1

-- 2ª solución
-- ===========

namespace Solucion2

lemma aux : ∀ m ≥ 4, m ^ 2 ≤ 2 ^ m := by
  intro m hm
  -- m : ℕ
  -- hm : m ≥ 4
  -- ⊢ m ^ 2 ≤ 2 ^ m
  induction m, hm using Nat.le_induction with
  | base =>
    -- ⊢ 4 ^ 2 ≤ 2 ^ 4
    grind
  | succ n hn hi =>
    -- n : ℕ
    -- hn : 4 ≤ n
    -- hi : n ^ 2 ≤ 2 ^ n
    -- ⊢ (n + 1) ^ 2 ≤ 2 ^ (n + 1)
    have h1 : 2 * n + 1 ≤ n ^ 2 := by
      calc 2 * n + 1
           ≤ 2 * n + 8     := by grind
      _    ≤ 2 * n + 2 * n := by grind
      _    = 4 * n         := by grind
      _    ≤ n * n         := by gcongr
      _    = n ^ 2         := by grind
    calc (n + 1) ^ 2
         = n ^ 2 + 2 * n + 1 := by grind
    _    ≤ n ^ 2 + n ^ 2     := Nat.add_le_add_left h1 (n ^ 2)
    _    = 2 * n ^ 2         := by grind
    _    ≤ 2 * 2 ^ n         := Nat.mul_le_mul_left 2 hi
    _    = 2 ^ (n + 1)       := by ring

example : ∃ k : ℕ, ∀ n : ℕ, (n + k) ^ 2 ≤ 2 ^ (n + k) := by
  use 4
  -- ⊢ ∀ (n : ℕ), (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  intro n
  -- ⊢ (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  exact aux (n + 4) (by grind)

end Solucion2

-- 3ª solución
-- ===========

namespace Solucion3

lemma aux : ∀ m ≥ 4, m ^ 2 ≤ 2 ^ m := by
  intro m hm
  -- m : ℕ
  -- hm : m ≥ 4
  -- ⊢ m ^ 2 ≤ 2 ^ m
  induction m, hm using Nat.le_induction with
  | base =>
    -- ⊢ 4 ^ 2 ≤ 2 ^ 4
    norm_num
  | succ n hn hi =>
    -- n : ℕ
    -- hn : 4 ≤ n
    -- hi : n ^ 2 ≤ 2 ^ n
    -- ⊢ (n + 1) ^ 2 ≤ 2 ^ (n + 1)
    have h1 : 2 * n + 1 ≤ n ^ 2 := by
      calc 2 * n + 1
           ≤ 2 * n + 8     := by omega
      _    ≤ 2 * n + 2 * n := by omega
      _    = 4 * n         := by ring
      _    ≤ n * n         := by gcongr
      _    = n ^ 2         := by ring
    calc (n + 1) ^ 2
         = n ^ 2 + 2 * n + 1 := by ring
    _    ≤ n ^ 2 + n ^ 2     := Nat.add_le_add_left h1 (n ^ 2)
    _    = 2 * n ^ 2         := by ring
    _    ≤ 2 * 2 ^ n         := Nat.mul_le_mul_left 2 hi
    _    = 2 ^ (n + 1)       := by ring

example : ∃ k : ℕ, ∀ n : ℕ, (n + k) ^ 2 ≤ 2 ^ (n + k) := by
  use 4
  -- ⊢ ∀ (n : ℕ), (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  intro n
  -- ⊢ (n + 4) ^ 2 ≤ 2 ^ (n + 4)
  exact aux (n + 4) (by omega)

end Solucion3

-- 4ª solución
-- ===========

namespace Solucion4

lemma aux : ∀ m ≥ 4, m ^ 2 ≤ 2 ^ m := by
  intro m hm
  -- m : ℕ
  -- hm : m ≥ 4
  -- ⊢ m ^ 2 ≤ 2 ^ m
  induction m, hm using Nat.le_induction with
  | base =>
    -- ⊢ 4 ^ 2 ≤ 2 ^ 4
    norm_num
  | succ n hn hi =>
    -- n : ℕ
    -- hn : 4 ≤ n
    -- hi : n ^ 2 ≤ 2 ^ n
    -- ⊢ (n + 1) ^ 2 ≤ 2 ^ (n + 1)
    have h1 : 2 * n + 1 ≤ n ^ 2 := by
      calc 2 * n + 1
           ≤ 2 * n + 8     := Nat.add_le_add_iff_left.mpr (by norm_num)
      _    = 2 * n + 2 * 4 := Nat.add_left_inj.mpr rfl
      _    ≤ 2 * n + 2 * n := Nat.add_le_add_iff_left.mpr (Nat.mul_le_mul_left 2 hn)
      _    = (2 + 2) * n   := (Nat.add_mul 2 2 n).symm
      _    = 4 * n         := congrArg (· * n) (Nat.succ_add 1 2)
      _    ≤ n * n         := Nat.mul_le_mul_right n hn
      _    = n ^ 2         := (Nat.pow_two n).symm
    calc (n + 1) ^ 2
         = n ^ 2 + 2 * n + 1 := by ring
    _    ≤ n ^ 2 + n ^ 2     := Nat.add_le_add_left h1 (n ^ 2)
    _    = 2 * n ^ 2         := (Nat.two_mul (n ^ 2)).symm
    _    ≤ 2 * 2 ^ n         := Nat.mul_le_mul_left 2 hi
    _    = 2 ^ (n + 1)       := Nat.pow_succ'.symm

example : ∃ k : ℕ, ∀ n : ℕ, (n + k) ^ 2 ≤ 2 ^ (n + k) :=
  ⟨4, fun n => aux (n + 4) (by omega)⟩

end Solucion4

-- Lemas usados
-- ============

variable (n m k : ℕ)
#check (Nat.add_le_add_iff_left : n + m ≤ n + k ↔ m ≤ k)
#check (Nat.add_le_add_left : n ≤ m → ∀ k, k + n ≤ k + m)
#check (Nat.add_left_inj : m + n = k + n ↔ m = k)
#check (Nat.add_mul n m k : (n + m) * k = n * k + m * k)
#check (Nat.mul_le_mul_left k : n ≤ m → k * n ≤ k * m)
#check (Nat.mul_le_mul_right k : n ≤ m → n * k ≤ m * k)
#check (Nat.pow_succ' : m ^ n.succ = m * m ^ n)
#check (Nat.pow_two n : n ^ 2 = n * n)
#check (Nat.succ_add n m : n.succ + m = (n + m).succ)
#check (Nat.two_mul n : 2 * n = n + n)
