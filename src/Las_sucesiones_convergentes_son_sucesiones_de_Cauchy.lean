-- Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.lean
-- Las sucesiones convergentes son sucesiones de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define
-- + a es un límite de la sucesión u , por
--      def limite (u : ℕ → ℝ) (a : ℝ) :=
--        ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| ≤ ε
-- + la sucesión u es convergente por
--      def suc_convergente (u : ℕ → ℝ) :=
--        ∃ a, limite u a
-- + la sucesión u es de Cauchy por
--      def suc_Cauchy (u : ℕ → ℝ) :=
--        ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε
--
-- Demostrar que las sucesiones convergentes son de Cauchy.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que existe un N ∈ ℕ
-- tal que
--    (∀ p ≥ N)(∀ q ≥ N)[|u(p) - u(q)| < ε]                          (1)
--
-- Puesto que u es convergente, existe un a ∈ ℝ tal que el límite de u
-- es a. Por tanto, existe un N ∈ ℕ tal que
--    (∀ n ≥ N)[|u(n) - a| < ε/2]                                    (2)
--
-- Para demostrar que con dicho N se cumple (1), sean p, q ∈ ℕ tales que
-- p ≥ N y q ≥ N. Entonces, por (2), se tiene que
--    |u(p) - a| < ε/2                                               (3)
--    |u(q) - a| < ε/2                                               (4)
-- Por tanto,
--    |u(p) - u(q)| = |(u(p) - a) + (a - u(q))|
--                  ≤ |u(p) - a|  + |a - u(q)|
--                  = |u(p) - a|  + |u(q) - a|
--                  < ε/2 + ε/2                    [por (3) y (4)
--                  = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ }

def limite (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def suc_Cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

-- 1ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  unfold suc_Cauchy
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  have hε2 : 0 < ε/2 := half_pos hε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) hε2 with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha hε2
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := congrArg (|u p - a| + .) (abs_sub_comm a (u q))
     _ < ε/2 + ε/2               := add_lt_add (hN p hp) (hN q hq)
     _ = ε                       := add_halves ε

-- 2ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := congrArg (|u p - a| + .) (abs_sub_comm a (u q))
     _ < ε/2 + ε/2               := add_lt_add (hN p hp) (hN q hq)
     _ = ε                       := add_halves ε

-- 3ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  have cota1 : |u p - a| < ε / 2 := hN p hp
  have cota2 : |u q - a| < ε / 2 := hN q hq
  clear hN hp hq
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by rw [abs_sub_comm a (u q)]
     _ < ε                       := by linarith

-- 4ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by rw [abs_sub_comm a (u q)]
     _ < ε                       := by linarith [hN p hp, hN q hq]

-- 5ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (by linarith) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by simp [abs_sub_comm]
     _ < ε                       := by linarith [hN p hp, hN q hq]

-- Lemas usados
-- ============

-- variable (a b c d x y : ℝ)
-- variable (f : ℝ → ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (congrArg f : x = y → f x = f y)
-- #check (half_pos : 0 < a → 0 < a / 2)
