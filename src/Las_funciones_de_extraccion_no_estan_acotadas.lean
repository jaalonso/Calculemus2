-- Las_funciones_de_extraccion_no_estan_acotadas.lean
-- Las funciones de extracción no están acotadas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción ϕ tal que ϕ(n) = 2*n.
--
-- En Lean4, se puede definir que ϕ es una función de extracción por
--    def extraccion (ϕ : ℕ → ℕ) :=
--      ∀ n m, n < m → ϕ n < ϕ m
--
-- Demostrar que las funciones de extracción no están acotadas; es decir,
-- que si ϕ es una función de extracción, entonces
--     ∀ N N', ∃ n ≥ N', ϕ n ≥ N
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración se usará como lema auxiliar el resultado del
-- ejercicio anterior; es decir, que si ϕ es una función de extracción,
-- entonces
--    (∀ n)[n ≤ ϕ(n)]
--
-- Sea ϕ una función de extracción y N, N' ∈ ℕ. Definimos
--    n = máx(N, N')
-- Entonces de tiene que
--    n ≥ N'
-- y, además,
--    N ≤ n
--      ≤ ϕ(n)    [por el Lema]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ n m, n < m → ϕ n < ϕ m

-- En la demostración se usará el siguiente lema auxiliar, demostrado en
-- el ejercicio anterior

lemma aux
  (h : extraccion ϕ)
  : ∀ n, n ≤ ϕ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (ϕ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ ϕ m        := HI
         _ < ϕ (succ m) := h m (m+1) (lt_add_one m)

-- 1ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  let n := max N N'
  use n
  -- ⊢ n ≥ N' ∧ ϕ n ≥ N
  constructor
  . -- ⊢ n ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ n ≥ N
    calc N ≤ n   := le_max_left N N'
         _ ≤ ϕ n := aux h n

-- 2ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  let n := max N N'
  use n
  -- ⊢ n ≥ N' ∧ ϕ n ≥ N
  constructor
  . -- ⊢ n ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ n ≥ N
    exact le_trans (le_max_left N N')
                   (aux h n)

-- 3ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  use max N N'
  -- ⊢ max N N' ≥ N' ∧ ϕ (max N N') ≥ N
  constructor
  . -- ⊢ max N N' ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ (max N N') ≥ N
    exact le_trans (le_max_left N N')
                   (aux h (max N N'))

-- 4ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  use max N N'
  -- ⊢ max N N' ≥ N' ∧ ϕ (max N N') ≥ N
  exact ⟨le_max_right N N',
         le_trans (le_max_left N N')
                  (aux h (max N N'))⟩

-- 5ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
fun N N' ↦ ⟨max N N', ⟨le_max_right N N',
                       le_trans (le_max_left N N')
                                (aux h (max N N'))⟩⟩

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
