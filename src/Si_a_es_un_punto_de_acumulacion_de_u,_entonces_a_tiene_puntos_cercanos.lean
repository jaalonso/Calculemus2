-- Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.lean
-- Si a es un punto de acumulación de u, entonces (∀ε>0)(∀n∈ℕ)(∃k≥n)[u(k)−a| < ε]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-julio-2024
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
-- También se puede definir que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ n, ∀ k ≥ n, |u k - a| < ε
--
-- Los puntos de acumulación de una sucesión son los límites de sus
-- subsucesiones. En Lean se puede definir por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
--
-- Demostrar que si a es un punto de acumulación de u, entonces
--    ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos el siguiente lema demostrado en el
-- ejercicio anterior: Si φ es una función de extracción, entonces
--    (∀ N, N')(∃ n ≥ N')[φ(n) ≥ N]

-- Por ser a un punto de acumulación, existe una función de extracción φ
-- tal que a es el límite de (u ∘ φ). Luego, para cada ε > 0, existe un
-- n' ∈ N tal que para todo k ≥ n',
--    |(u ∘ φ)(k) - a| < ε                                           (1)
-- Por el lema 2, existe un m ∈ ℕ tal que
--    m ≥ n'                                                         (2)
--    φ(m) ≥ n                                                       (3)
-- Entonces, por (2) y (1),
--    |(u ∘ φ)(m) - a| < ε                                           (4)
-- Luego, por (3) y (4), se tiene que
--    φ(m) ≥ n ∧ |u(φ)(m)) - a| < ε
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ n, ∀ k ≥ n, |u k - a| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- En la demostración se usarán los siguientes lemas demostrados en
-- ejercicios anteriores.

lemma aux1
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (φ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ φ m        := HI
         _ < φ (succ m) := h m (m+1) (lt_add_one m)

lemma aux2
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
fun N N' ↦ ⟨max N N', ⟨le_max_right N N',
                       le_trans (le_max_left N N')
                                (aux1 h (max N N'))⟩⟩

-- 1ª demostración
-- ===============

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε :=
by
  intros ε hε n
  -- ε : ℝ
  -- hε : ε > 0
  -- n : ℕ
  -- ⊢ ∃ k, k ≥ n ∧ |u k - a| < ε
  unfold punto_acumulacion at h
  -- h : ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
  rcases h with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : limite (u ∘ φ) a
  unfold limite at hφ2
  -- hφ2 : ∀ (ε : ℝ), ε > 0 → ∃ n, ∀ (k : ℕ), k ≥ n → |(u ∘ φ) k - a| < ε
  cases' hφ2 ε hε with n' hn'
  -- n' : ℕ
  -- hn' : ∀ (k : ℕ), k ≥ n' → |(u ∘ φ) k - a| < ε
  rcases aux2 hφ1 n n' with ⟨m, hm, hm'⟩
  -- m : ℕ
  -- hm : m ≥ n'
  -- hm' : φ m ≥ n
  clear hφ1 hφ2
  use φ m
  -- ⊢ φ m ≥ n ∧ |u (φ m) - a| < ε
  constructor
  . -- ⊢ φ m ≥ n
    exact hm'
  . -- ⊢ |u (φ m) - a| < ε
    exact hn' m hm

-- 2ª demostración
-- ===============

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε :=
by
  intros ε hε n
  -- ε : ℝ
  -- hε : ε > 0
  -- n : ℕ
  -- ⊢ ∃ k, k ≥ n ∧ |u k - a| < ε
  rcases h with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : limite (u ∘ φ) a
  cases' hφ2 ε hε with n' hn'
  -- n' : ℕ
  -- hn' : ∀ (k : ℕ), k ≥ n' → |(u ∘ φ) k - a| < ε
  rcases aux2 hφ1 n n' with ⟨m, hm, hm'⟩
  -- m : ℕ
  -- hm : m ≥ n'
  -- hm' : φ m ≥ n
  use φ m
  -- ⊢ φ m ≥ n ∧ |u (φ m) - a| < ε
  exact ⟨hm', hn' m hm⟩

-- 3ª demostración
-- ===============

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε :=
by
  intros ε hε n
  -- ε : ℝ
  -- hε : ε > 0
  -- n : ℕ
  -- ⊢ ∃ k, k ≥ n ∧ |u k - a| < ε
  rcases h with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : limite (u ∘ φ) a
  cases' hφ2 ε hε with n' hn'
  -- n' : ℕ
  -- hn' : ∀ (k : ℕ), k ≥ n' → |(u ∘ φ) k - a| < ε
  rcases aux2 hφ1 n n' with ⟨m, hm, hm'⟩
  -- m : ℕ
  -- hm : m ≥ n'
  -- hm' : φ m ≥ n
  exact ⟨φ m, hm', hn' _ hm⟩

-- 4ª demostración
-- ===============

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε :=
by
  intros ε hε n
  -- ε : ℝ
  -- hε : ε > 0
  -- n : ℕ
  -- ⊢ ∃ k, k ≥ n ∧ |u k - a| < ε
  rcases h with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : limite (u ∘ φ) a
  cases' hφ2 ε hε with n' hn'
  -- n' : ℕ
  -- hn' : ∀ (k : ℕ), k ≥ n' → |(u ∘ φ) k - a| < ε
  rcases aux2 hφ1 n n' with ⟨m, hm, hm'⟩
  -- m : ℕ
  -- hm : m ≥ n'
  -- hm' : φ m ≥ n
  use φ m
  -- ⊢ φ m ≥ n ∧ |u (φ m) - a| < ε
  aesop

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
