-- Reto_20.lean
-- Las subsucesiones tienen el mismo límite que la sucesión.
-- Sevilla, 28-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Una subsucesión se obtiene aplicando a la sucesión original una
-- función de extracción; es decir, una función φ : ℕ → ℕ
-- estrictamente creciente. Por ejemplo, la subsucesión
--    u₀, u₂, u₄, u₆, ...
-- se obtiene con la función de extracción φ definida por
-- φ(n) = 2n.
--
-- Las definiciones anteriores se formalizan en Lean 4 como:
--
--    -- φ es una función de extracción.
--    def extraccion (φ : ℕ → ℕ) :=
--      StrictMono φ
--
--    -- v es una subsucesión de u.
--    def subsucesion (v u : ℕ → ℝ) :=
--      ∃ φ, extraccion φ ∧ v = u ∘ φ
--
--    -- a es el límite de u.
--    def LimSuc (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |u n - a| < ε
--
-- El reto de esta semana consiste en demostrar en Lean 4 que toda
-- subsucesión de una sucesión convergente converge al mismo
-- límite que la sucesión. Para ello, completar la siguiente
-- teoría de Lean 4:
--    import Mathlib.Basic.Real.Basic
--
--    variable {u v : ℕ → ℝ}
--    variable {a : ℝ}
--
--    def extraccion (φ : ℕ → ℕ):=
--      StrictMono φ
--
--    def subsucesion (v u : ℕ → ℝ) :=
--      ∃ φ, extraccion φ ∧ v = u ∘ φ
--
--    def LimSuc (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |u n - a| < ε
--
--    example
--      (hv : subsucesion v u)
--      (ha : LimSuc u a)
--      : LimSuc v a :=
--    by sorry
-- ---------------------------------------------------------------


-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema: Si φ es una función de extracción,
-- entonces
--    ∀ n, n ≤ φ(n)
--
-- Por ser v una subsucesión de u, existe una función de
-- extracción φ tal que
--    v = u ∘ φ                                                (3)
--
-- Tenemos que demostrar que para cada ε > 0, existe un k ∈ ℕ tal
-- que
--     ∀ n ≥ k, |v(n) - a| < ε                                 (1)
--
-- Puesto que a es el límite de u, , existe un k ∈ ℕ tal
-- que
--     ∀ n ≥ k, |u(n) - a| < ε                                 (2)
--
-- Veamos que k verifica (1). Para ello, sea n ≥ k. Entonces,
--    φ(n) ≥ k                                                 (4)
-- ya que
--    φ(n) ≥ n    [por el Lema]
--         ≥ k
-- Luego,
--    |v(n) - a| = |(u ∘ φ )(n) - a|    [por (3)]
--               = |u(φ(n)) - a|
--               < ε                    [por (2) y (4)]

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic

variable {u v : ℕ → ℝ}
variable {a : ℝ}

-- φ es una función de extracción.
def extraccion (φ : ℕ → ℕ):=
  StrictMono φ

-- v es una subsucesión de u.
def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

-- a es el límite de u.
def LimSuc (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |u n - a| < ε

-- 1ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : LimSuc u a)
  : LimSuc v a :=
by
  obtain ⟨φ, hφ, hφ'⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : extraccion φ
  -- hφ' : v = u ∘ φ
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |v n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |v n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |v n - a| < ε
  have h1 : φ n ≥ k :=
    calc φ n
         ≥ n := StrictMono.le_apply hφ
       _ ≥ k := hn
  calc |v n - a|
       = |(u ∘ φ ) n  - a| := by rw [hφ']
     _ = |u (φ n) - a|     := rfl
     _ < ε                 := hk (φ n) h1

-- 2ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : LimSuc u a)
  : LimSuc v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : extraccion φ
  -- ⊢ LimSuc (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(u ∘ φ) n - a| < ε
  have h1 : φ n ≥ k :=
    calc φ n
         ≥ n := hφ.le_apply
       _ ≥ k := hn
  calc |(u ∘ φ) n  - a|
     _ = |u (φ n) - a|     := rfl
     _ < ε                 := hk (φ n) h1

-- 3ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : LimSuc u a)
  : LimSuc v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : extraccion φ
  -- ⊢ LimSuc (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hk
  -- ⊢ φ n ≥ k
  apply le_trans hn
  -- ⊢ n ≤ φ n
  exact hφ.le_apply

-- 4ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : LimSuc u a)
  : LimSuc v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : extraccion φ
  -- ⊢ LimSuc (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  exact ⟨k, fun n hn ↦ hk (φ n) (le_trans hn hφ.le_apply)⟩

-- Lemas usados
-- ============

/-
variable (m n x y z : ℕ)
#check (Nat.zero_le n : 0 ≤ n)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-/
