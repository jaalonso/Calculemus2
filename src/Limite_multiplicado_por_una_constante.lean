-- Limite_multiplicado_por_una_constante.lean
-- Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de cuₙ es ca
-- José A. Alonso Jiménez
-- Sevilla, 13 de febrero de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que que si el límite de uₙ es a, entonces el de
-- cuₙ es ca.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que
--    (∃ N ∈ ℕ)(∀ n ≥ N)[|cuₙ - ca| < ε]                             (1)
-- Distinguiremos dos casos según sea c = 0 o no.
--
-- Primer caso: Supongamos que c = 0. Entonces, (1) se reduce a
--    (∃ N ∈ ℕ)(∀ n ≥ N)[|0·uₙ - 0·a| < ε]
-- es decir,
--    (∃ N ∈ ℕ)(∀ n ≥ N)[0 < ε]
-- que se verifica para cualquier número N, ya que ε > 0.
--
-- Segundo caso: Supongamos que c ≠ 0. Entonces, ε/|c| > 0 y, puesto que
-- el límite de uₙ es a, existe un k ∈ ℕ tal que
--    (∀ n ≥ k)[|uₙ - a| < ε/|c|]                                    (2)
-- Veamos que con k se cumple (1). En efecto, sea n ≥ k. Entonces,
--    |cuₙ - ca| = |c(uₙ - a)|
--               = |c||u n - a|
--               < |c|(ε/|c|)     [por (2)]
--               = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    calc |c * u n - c * a|
         = |c * (u n - a)| := congr_arg abs (mul_sub c (u n) a).symm
       _ = |c| * |u n - a| := abs_mul c  (u n - a)
       _ < |c| * (ε / |c|) := (mul_lt_mul_left hc').mpr hN
       _ = ε               := mul_div_cancel₀ ε (ne_of_gt hc')

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    -- ⊢ |c * u n - c * a| < ε
    rw [← mul_sub]
    -- ⊢ |c * (u n - a)| < ε
    rw [abs_mul]
    -- ⊢ |c| * |u n - a| < ε
    rw [← lt_div_iff' hc']
    -- ⊢ |u n - a| < ε / |c|
    exact hN

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . subst hc
    intros ε hε
    aesop
  . intros ε hε
    have hc' : 0 < |c| := by aesop
    have hεc : 0 < ε / |c| := div_pos hε hc'
    cases' h (ε/|c|) hεc with N hN
    use N
    intros n hn
    specialize hN n hn
    dsimp only
    rw [← mul_sub, abs_mul, ← lt_div_iff' hc']
    exact hN

-- Lemas usados
-- ============

-- variable (b c : ℝ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b))
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
