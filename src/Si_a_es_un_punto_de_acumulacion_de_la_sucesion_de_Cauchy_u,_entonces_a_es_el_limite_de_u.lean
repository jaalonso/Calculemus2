-- Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.lean
-- Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción f tal que f(n) = 2*n.
--
-- En Lean4, se puede definir que f es una función de extracción por
--    def extraccion (f : ℕ → ℕ) :=
--      ∀ n m, n < m → f n < f m
-- que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
-- que a es un punto de acumulación de u por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ f, extraccion f ∧ limite (u ∘ f) a
-- que la sucesión u es de Cauchy por
--    def suc_cauchy (u : ℕ → ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε
--
-- Demostrar que si u es una sucesión de Cauchy y a es un punto de
-- acumulación de u, entonces a es el límite de u.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos el siguiente lema demostrado en un
-- ejercicio anterior: Si a es un punto de acumulación de u, entonces
--    (∀ ε > 0)(∀ N)(∃ n ≥ N) |u n - a| < ε
--
-- Sea ε > 0. Por ser u una sucesión de Cauchy, existe un N ∈ ℕ tal que
--    (∀ p ≥ N)(∀ q ≥ N)|u(p) - u(q)| < ε/2                          (1)
-- Vamos a demostrar que
--    (∀ n ≥ N)|u(n) - a| < ε
-- y, por tanto a es limite de u.
--
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ N                                                          (2)
-- Por el lema, existe un N' ∈ ℕ tal que
--    N' ≥ N                                                         (3)
--    |u(N') - a| < ε/2                                              (4)
-- Por tanto,
--    |u(n) - a| = |(u(n) - u(N')) + (u(N') - a)|
--               ≤ |u(n) - u(N')| + |u(N') - a|
--               < ε/2 + |u(N') - a|               [por (1), (2) y (3)]
--               < ε/2 + ε/2                       [por (4)]
--               = ε
-- De donde se tiene que
--    |u(n) - a| < ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}
variable {f : ℕ → ℕ}

def extraccion (f : ℕ → ℕ) :=
  ∀ n m, n < m → f n < f m

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ f, extraccion f ∧ limite (u ∘ f) a

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

lemma aux1
  (h : extraccion f)
  : ∀ n, n ≤ f n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (f 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ f m        := HI
         _ < f (succ m) := h m (m+1) (lt_add_one m)

lemma aux2
  (h : extraccion f)
  : ∀ N N', ∃ n ≥ N', f n ≥ N :=
fun N N' ↦ ⟨max N N', ⟨le_max_right N N',
                       le_trans (le_max_left N N')
                                (aux1 h (max N N'))⟩⟩

lemma cerca_acumulacion
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
by
  intros ε hε N
  rcases h with ⟨f, hf1, hf2⟩
  cases' hf2 ε hε with N' hN'
  rcases aux2 hf1 N N' with ⟨m, hm, hm'⟩
  exact ⟨f m, hm', hN' _ hm⟩

-- 1ª demostración
-- ===============

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  unfold suc_cauchy at hu
  -- hu : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' hu (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε / 2
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2 :=
    cerca_acumulacion ha (ε/2) (half_pos hε) N
  cases' ha' with N' h
  -- N' : ℕ
  -- h : N' ≥ N ∧ |u N' - a| < ε / 2
  cases' h with hNN' hN'
  -- hNN' : N' ≥ N
  -- hN' : |u N' - a| < ε / 2
  calc   |u n - a|
       = |(u n - u N') + (u N' - a)| := by ring_nf
     _ ≤ |u n - u N'| + |u N' - a|   := abs_add (u n - u N') (u N' - a)
     _ < ε/2 + |u N' - a|            := add_lt_add_right (hN n hn N' hNN') _
     _ < ε/2 + ε/2                   := add_lt_add_left hN' (ε / 2)
     _ = ε                           := add_halves ε

-- 2ª demostración
-- ===============

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  cases' hu (ε/2) (by linarith) with N hN
  -- N : ℕ
  -- hN : ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε / 2
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |u n - a| < ε
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2 := by
    apply cerca_acumulacion ha (ε/2) (by linarith)
  rcases ha' with ⟨N', hNN', hN'⟩
  -- N' : ℕ
  -- hNN' : N' ≥ N
  -- hN' : |u N' - a| < ε / 2
  calc  |u n - a|
      = |(u n - u N') + (u N' - a)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - a|   := abs_add (u n - u N') (u N' - a)
    _ < ε                           := by linarith [hN n hn N' hNN']

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- variable (b c : ℝ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_lt_add_left : b < c → ∀ (a : ℝ), a + b < a + c)
-- #check (add_lt_add_right : b < c → ∀ (a : ℝ), b + a < c + a)
-- #check (half_pos : 0 < a → 0 < a / 2)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
