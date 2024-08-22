-- Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.lean
-- Si uₙ está acotada y lim vₙ = 0, entonces lim (uₙ·vₙ) = 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si uₙ está acotada y lim vₙ = 0, entonces
-- lim (u·v)ₙ = 0.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar
--    (∃ k)(∀ n)[n ≥ k → |(u·v)ₙ - 0| < ε]                           (1)
--
-- Puesto que la sucesión u está acotada, existe un B ∈ ℝ tal que
--    (∀ n ∈ ℕ) |uₙ| ≤ B                                             (2)
-- Luego B ≥ 0. Lo demostraremos por caso según que B = 0 o B > 0.
--
-- Caso 1: Supongamos que B = 0. Entonces, por (2),
--    (∀ n ∈ ℕ) |uₙ| ≤ 0
-- Luego,
--    (∀ n ∈ ℕ) uₙ = 0                                               (3)
-- Para demostrar (1), para basta tomar 0 como k, ya que si n ≥ 0,
-- entonces
--    |(u·v)ₙ - 0| = |uₙ·vₙ|
--                 = |0·vₙ|     [por (3)
--                 = 0
--                 < ε
--
-- Caso 2: Supongamos que B > 0. Entonces, ε/B > 0 y, puesto que
-- lim vₙ = 0, existe un k ∈ ℕ tal que
--    (∀ n)[n ≥ k → |vₙ - 0| < ε/B]                                  (4)
-- Para demostrar (1), para basta el mismo k, ya que si n ≥ k,
-- entonces
--    |(u·v)ₙ - 0| = |uₙ·vₙ|
--                 = |uₙ|·|vₙ|
--                 ≤ B·|vₙ|       [por (2)]
--                 < B·(ε/B)      [por (4)]
--                 = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a : ℝ)

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
  ∃ B, ∀ n, |a n| ≤ B

-- 1ª demostración
-- ===============

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
by
  cases' hU with B hB
  -- B : ℝ
  -- hB : ∀ (n : ℕ), |u n| ≤ B
  have hBnoneg : 0 ≤ B :=
    calc 0 ≤ |u 0| := abs_nonneg (u 0)
         _ ≤ B     := hB 0
  by_cases hB0 : B = 0
  . -- hB0 : B = 0
    subst hB0
    -- hB : ∀ (n : ℕ), |u n| ≤ 0
    -- hBnoneg : 0 ≤ 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    use 0
    -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(u * v) n - 0| < ε
    intros n _hn
    -- n : ℕ
    -- hn : n ≥ 0
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n * v n|   := congr_arg abs (Pi.mul_apply u v n)
       _ = |u n| * |v n| := abs_mul (u n) (v n)
       _ ≤ 0 * |v n|     := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
       _ = 0             := zero_mul (|v n|)
       _ < ε             := hε
  . -- hB0 : ¬B = 0
    change B ≠ 0 at hB0
    -- hB0 : B ≠ 0
    have hBpos : 0 < B := (Ne.le_iff_lt hB0.symm).mp hBnoneg
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    cases' hV (ε/B) (div_pos hε hBpos) with k hk
    -- k : ℕ
    -- hk : ∀ (n : ℕ), n ≥ k → |v n - 0| < ε / B
    use k
    -- ⊢ ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n * v n|    := congr_arg abs (Pi.mul_apply u v n)
       _ = |u n| * |v n|  := abs_mul (u n) (v n)
       _ ≤ B * |v n|      := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
       _ < B * (ε/B)      := mul_lt_mul_of_pos_left (hk n hn) hBpos
       _ = ε              := mul_div_cancel₀ ε hB0

-- 2ª demostración
-- ===============

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
by
  cases' hU with B hB
  -- B : ℝ
  -- hB : ∀ (n : ℕ), |u n| ≤ B
  have hBnoneg : 0 ≤ B :=
    calc 0 ≤ |u 0| := abs_nonneg (u 0)
         _ ≤ B     := hB 0
  by_cases hB0 : B = 0
  . subst hB0
    -- hB : ∀ (n : ℕ), |u n| ≤ 0
    -- hBnoneg : 0 ≤ 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    use 0
    -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(u * v) n - 0| < ε
    intros n _hn
    -- n : ℕ
    -- _hn : n ≥ 0
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n| * |v n| := by aesop
       _ ≤ 0 * |v n|     := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
       _ = 0             := by ring
       _ < ε             := hε
  . -- hB0 : ¬B = 0
    change B ≠ 0 at hB0
    -- hB0 : B ≠ 0
    have hBpos : 0 < B := (Ne.le_iff_lt hB0.symm).mp hBnoneg
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    cases' hV (ε/B) (div_pos hε hBpos) with k hk
    -- k : ℕ
    -- hk : ∀ (n : ℕ), n ≥ k → |v n - 0| < ε / B
    use k
    -- ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n| * |v n|  := by simp [Pi.mul_apply, abs_mul]
       _ ≤ B * |v n|      := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
       _ < B * (ε/B)      := by aesop
       _ = ε              := mul_div_cancel₀ ε hB0

-- Lemas usados
-- ============

-- #variable (n : ℕ)
-- #variable (a b c : ℝ)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (Ne.le_iff_lt : a ≠ b → (a ≤ b ↔ a < b))
-- #check (Pi.mul_apply u v n : (u * v) n = u n * v n)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
-- #check (mul_lt_mul_of_pos_left : b < c → 0 < a → a * b < a * c)
-- #check (sub_zero a : a - 0 = a)
-- #check (zero_mul a : 0 * a = 0)
