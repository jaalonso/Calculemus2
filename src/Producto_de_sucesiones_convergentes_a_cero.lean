-- Producto_de_sucesiones_convergentes_a_cero.lean
-- Si uₙ y vₙ convergen a 0, entonces uₙvₙ converge a 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que si las sucesiones u(n) y v(n) convergen a cero,
-- entonces u(n)·v(n) también converge a cero.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos ue demostrar que
--    (∃N ∈ ℕ)(∀n ≥ N)[|(uv)(n) - 0| < ε]                         (1)
-- Puesto que el límite de uₙ es 0, existe un U ∈ ℕ tal que
--    (∀n ≥ U)[|u(n) - 0| < ε]                                       (2)
-- y, puesto que el límite de vₙ es 0, existe un V ∈ ℕ tal que
--    (∀n ≥ V)[|v(n) - 0| < 1]                                       (3)
-- Entonces, N = max(U, V) cumple (1). En efecto, sea n ≥ N. Entonces,
-- n ≥ U y n ≥ V y, aplicando (2) y (3), se tiene
--    |u(n) - 0| < ε                                                 (4)
--    |v(n) - 0| < 1                                                 (5)
-- Por tanto,
--    |(u·v)(n) - 0| = |u(n)·v(n)|
--                   = |u(n)|·|v n|
--                   < ε·1             [por (4) y (5)]
--                   = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 zero_lt_one with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n - 0| < ε
  -- hV : |v n - 0| < 1
  -- ⊢ |(u * v) n - 0| < ε
  calc |(u * v) n|
       = |u n * v n|   := rfl
     _ = |u n| * |v n| := abs_mul (u n) (v n)
     _ < ε * 1         := mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
     _ = ε             := mul_one ε

-- 2ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 (by linarith) with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n| < ε
  -- hV : |v n| < 1
  -- ⊢ |(u * v) n| < ε
  calc |(u * v) n|
       = |u n * v n|   := rfl
     _ = |u n| * |v n| := abs_mul (u n) (v n)
     _ < ε * 1         := by { apply mul_lt_mul'' hU hV <;> simp [abs_nonneg] }
     _ = ε             := mul_one ε

-- 3ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 (by linarith) with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  have hUN : U ≤ N := le_max_left U V
  have hVN : V ≤ N := le_max_right U V
  specialize hU n (by linarith)
  -- hU : |u n - 0| < ε
  specialize hV n (by linarith)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n| < ε
  -- hV : |v n| < 1
  -- ⊢ |(u * v) n| < ε
  rw [Pi.mul_apply]
  -- ⊢ |u n * v n| < ε
  rw [abs_mul]
  -- ⊢ |u n| * |v n| < ε
  convert mul_lt_mul'' hU hV _ _ using 2 <;> simp

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- variable (I : Type _)
-- variable (f : I → Type _)
-- #check (zero_lt_one : 0 < 1)
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (sub_zero a : a - 0 = a)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (mul_one a : a * 1 = a)
