-- Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean
-- Las subsucesiones tienen el mismo límite que la sucesión.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.
--
-- En Lean4, se puede definir que φ es una función de extracción por
--    def extraccion (φ : ℕ → ℕ) :=
--      ∀ n m, n < m → φ n < φ m
-- que v es una subsucesión de u por
--    def subsucesion (v u : ℕ → ℝ) :=
--      ∃ φ, extraccion φ ∧ v = u ∘ φ
-- y que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
--
-- Demostrar que las subsucesiones de una sucesión convergente tienen el
-- mismo límite que la sucesión.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema demostrado en un ejercicio anterior: Si φ
-- es una función de extracción, entonces
--    (∀ n)[n ≤ φ(n)]
--
-- Por ser v una subsucesión de u, existe una función de extracción φ tal
-- que
--    v = u ∘ φ                                                      (1)
-- Sea a el límite de u y tenemos que demostrar que también lo es de
-- v. Para ello, sea ε > 0. Por ser a límite de u, existe un N ∈ ℕ tal
-- que
--    (∀ k ≥ N)[|u(k) - a| < ε]                                      (2)
-- Vamos a demostrar que
--    (∀ n ≥ N)[|v(n) - a| < ε]
-- Para ello, sea n ≥ N. Entonces,
--    φ(n) ≥ N
-- ya que
--    φ(n) ≥ n    [por el Lema]
--         ≥ N                                                       (3)
-- Luego,
--    |v(n) - a| = |(u ∘ φ )(n) - a|    [por (1)
--               = |u(φ(n)) - a|
--               < ε                    [por (2) y (3)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Nat

variable {u v : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

-- En la demostración se usará el siguiente lema demostrado en un
-- ejercicio anterior.
lemma aux
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (φ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ φ m        := HI
         _ < φ (succ m) := h m (m+1) (lt_add_one m)

-- 1ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have h1 : φ n ≥ N := calc
    φ n ≥ n := by exact aux hφ1 n
      _ ≥ N := hn
  calc |v n  - a| = |(u ∘ φ ) n  - a| := by {congr ; exact congrFun hφ2 n}
                _ = |u (φ n) - a|     := rfl
                _ < ε                 := hN (φ n) h1

-- 2ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  unfold limite at ha
  -- ha : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  unfold subsucesion at hv
  -- hv : ∃ φ, extraccion φ ∧ v = u ∘ φ
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hN
  -- ⊢ φ n ≥ N
  apply le_trans hn
  -- ⊢ n ≤ φ n
  exact aux hφ1 n

-- 3ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |v n - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hN
  -- ⊢ φ n ≥ N
  exact le_trans hn (aux hφ1 n)

-- 4ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |v n - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  exact hN (φ n) (le_trans hn (aux hφ1 n))

-- 5ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  exact fun n hn ↦ hN (φ n) (le_trans hn (aux hφ1 n))

-- 6ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  exact ⟨N, fun n hn ↦ hN (φ n) (le_trans hn (aux hφ1 n))⟩

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
