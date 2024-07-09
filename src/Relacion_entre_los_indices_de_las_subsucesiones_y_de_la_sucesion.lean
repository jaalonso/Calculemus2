-- Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.lean
-- Relación entre los índices de las subsucesiones y los de la sucesión.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción ϕ tal que ϕ(n) = 2*n.
--
-- En Lean4, se puede definir que ϕ es una función de extracción por
--    def extraccion (ϕ : ℕ → ℕ) :=
--      ∀ {n m}, n < m → ϕ n < ϕ m
--
-- Demostrar que si ϕ es una función de extracción, entonces
--    ∀ n, n ≤ ϕ n
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por inducción en n.
--
-- Base de la inducción: Como 0 es el menor número natural, se tiene que
--    0 ≤ ϕ(0)
--
-- Paso de inducción: Sea m ∈ ℕ y supongamos que la hipótesis de inducción
--    m ≤ ϕ(m)                                                      (HI)
-- Puesto que ϕ es una función de extracción,
--    ϕ(m) < ϕ(m+1)                                                 (1)
-- De (HI) y (1) se tiene que
--    m < ϕ(m+1)
-- Por tanto,
--    m+1 ≤ ϕ(m+1)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ {n m}, n < m → ϕ n < ϕ m

-- 1ª demostración
-- ===============

example :
  extraccion ϕ → ∀ n, n ≤ ϕ n :=
by
  intros h n
  -- h : extraccion ϕ
  -- n : ℕ
  -- ⊢ n ≤ ϕ n
  induction' n with m HI
  . -- ⊢ zero ≤ ϕ zero
    exact Nat.zero_le (ϕ 0)
  . -- m : ℕ
    -- HI : m ≤ ϕ m
    -- ⊢ succ m ≤ ϕ (succ m)
    apply Nat.succ_le_of_lt
    -- ⊢ m < ϕ (succ m)
    have h1 : m < succ m := lt_add_one m
    calc m ≤ ϕ m        := HI
         _ < ϕ (succ m) := h h1

-- 2ª demostración
-- ===============

example :
  extraccion ϕ → ∀ n, n ≤ ϕ n :=
by
  intros h n
  -- h : extraccion ϕ
  -- n : ℕ
  -- ⊢ n ≤ ϕ n
  induction' n with m HI
  . -- ⊢ zero ≤ ϕ zero
    exact Nat.zero_le (ϕ 0)
  . -- ⊢ succ m ≤ ϕ (succ m)
    have h1 : m < ϕ (succ m) :=
      calc m ≤ ϕ m        := HI
           _ < ϕ (succ m) := h (lt_add_one m)
    exact Nat.succ_le_of_lt h1

-- Lemas usados
-- ============

-- variable (m n : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (lt_add_one n : n < n + 1)
