-- Unicidad_del_limite_de_las_sucesiones_convergentes.lean
-- Unicidad del límite de las sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 6 de febrero de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--    λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
--
-- Demostrar que cada sucesión tiene como máximo un límite.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que si u es una sucesión y a y b son límites de
-- u, entonces a = b. Para ello, basta demostrar que a ≤ b y b ≤ a.

-- Demostraremos que b ≤ a por reducción al absurdo. Supongamos que b ≰ a.
-- Sea ε = b - a. Entonces, ε/2 > 0 y, puesto que a es un límite de u,
-- existe un A ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ A → |u(n) - a| < ε/2]                             (1)
-- y, puesto que b también es un límite de u, existe un B ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ B → |u(n) - b| < ε/2]                             (2)
-- Sea N = máx(A, B). Entonces, N ≥ A y N ≥ B y, por (2) y (3), se tiene
--    |u(N) - a| < ε/2                                               (3)
--    |u(N) - b| < ε/2                                               (4)
--
-- Para obtener una contradicción basta probar que ε < ε. Su prueba es
--    ε = b - a
--      = |b - a|
--      = |(b - a) + (u(N) - u(N))|
--      = |(u(N) - a) + (b - u(N))|
--      ≤ |u(N) - a| + |b - u(N)|
--      = |u(N) - a| + |u(N) - b|
--      < ε/2 + ε/2                   [por (3) y (4)]
--      = ε
--
-- La demostración de a ≤ b es análoga a la anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a b : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración del lema auxiliar
-- =================================

example
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
by
  by_contra h
  -- h : ¬b ≤ a
  -- ⊢ False
  let ε := b - a
  have hε : ε > 0 := sub_pos.mpr (not_le.mp h)
  have hε2 : ε / 2 > 0 := half_pos hε
  cases' ha (ε/2) hε2 with A hA
  -- A : ℕ
  -- hA : ∀ (n : ℕ), n ≥ A → |u n - a| < ε / 2
  cases' hb (ε/2) hε2 with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), n ≥ B → |u n - b| < ε / 2
  let N := max A B
  have hAN : A ≤ N := le_max_left A B
  have hBN : B ≤ N := le_max_right A B
  specialize hA N hAN
  -- hA : |u N - a| < ε / 2
  specialize hB N hBN
  -- hB : |u N - b| < ε / 2
  have h2 : ε < ε := by calc
    ε = b - a                   := rfl
    _ = |b - a|                 := (abs_of_pos hε).symm
    _ = |(b - a) + 0|           := by {congr ; exact (add_zero (b - a)).symm}
    _ = |(b - a) + (u N - u N)| := by {congr ; exact (sub_self (u N)).symm}
    _ = |(u N - a) + (b - u N)| := congrArg (fun x => |x|) (by ring)
    _ ≤ |u N - a| + |b - u N|   := abs_add (u N - a) (b - u N)
    _ = |u N - a| + |u N - b|   := congrArg (|u N - a| + .) (abs_sub_comm b (u N))
    _ < ε / 2 + ε / 2           := add_lt_add hA hB
    _ = ε                       := add_halves ε
  have h3 : ¬(ε < ε) := lt_irrefl ε
  show False
  exact h3 h2

-- 2ª demostración del lema auxiliar
-- =================================

lemma aux
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
by
  by_contra h
  -- h : ¬b ≤ a
  -- ⊢ False
  let ε := b - a
  cases' ha (ε/2) (by linarith) with A hA
  -- A : ℕ
  -- hA : ∀ (n : ℕ), n ≥ A → |u n - a| < ε / 2
  cases' hb (ε/2) (by linarith) with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), n ≥ B → |u n - b| < ε / 2
  let N := max A B
  have hAN : A ≤ N := le_max_left A B
  have hBN : B ≤ N := le_max_right A B
  specialize hA N hAN
  -- hA : |u N - a| < ε / 2
  specialize hB N hBN
  -- hB : |u N - b| < ε / 2
  rw [abs_lt] at hA hB
  -- hA : -(ε / 2) < u N - a ∧ u N - a < ε / 2
  -- hB : -(ε / 2) < u N - b ∧ u N - b < ε / 2
  linarith

-- 1ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (aux hb ha) (aux ha hb)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (sub_pos : 0 < a - b ↔ b < a)
-- #check (half_pos : a > 0 → a / 2 > 0)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
-- #check (abs_of_pos : 0 < a → |a| = a)
-- #check (add_zero a : a + 0 = a)
-- #check (sub_self a : a - a = 0)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (lt_irrefl a : ¬a < a)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
