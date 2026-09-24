-- Reto_19.lean
-- Las sucesiones convergentes son sucesiones de Cauchy.
-- Sevilla, 16-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que las sucesiones convergentes son de Cauchy.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que existe un
-- k ∈ ℕ tal que
--    ∀ p ≥ k, ∀ q ≥ k, |u(p) - u(q)| < ε                      (1)
--
-- Puesto que u es convergente, existe un a ∈ ℝ tal que el límite
-- de u es a. Por tanto, existe un k ∈ ℕ tal que
--    ∀ n ≥ k, |u(n) - a| < ε/2                                (2)
--
-- Para demostrar que con dicho k se cumple (1), sean p, q ∈ ℕ
-- tales que p ≥ k y q ≥ k. Entonces, por (2), se tiene que
--    |u(p) - a| < ε/2                                         (3)
--    |u(q) - a| < ε/2                                         (4)
-- Por tanto,
--    |u(p) - u(q)| = |(u(p) - a) + (a - u(q))|
--                  ≤ |u(p) - a|  + |a - u(q)|
--                  = |u(p) - a|  + |u(q) - a|
--                  < ε/2 + ε/2                    [por (3) y (4)]
--                  = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}

def LimSuc (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def SucConvergente (u : ℕ → ℝ) :=
  ∃ a, LimSuc u a

def SucCauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ k, ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε

-- 1ª demostración
-- ===============

example
  (h : SucConvergente u)
  : SucCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : LimSuc u a
  obtain ⟨k, hk⟩ := ha (ε/2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε / 2
  use k
  -- ⊢ ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ k
  -- q : ℕ
  -- hq : q ≥ k
  -- ⊢ |u p - u q| < ε
  grind

-- 2ª demostración
-- ===============

example
  (h : SucConvergente u)
  : SucCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : LimSuc u a
  obtain ⟨k, hk⟩ := ha (ε/2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε / 2
  use k
  -- ⊢ ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ k
  -- q : ℕ
  -- hq : q ≥ k
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by grind
     _ ≤ |u p - a|  + |a - u q|  := by grind
     _ = |u p - a|  + |u q - a|  := by grind
     _ < ε                       := by grind

-- 3ª demostración
-- ===============

example
  (h : SucConvergente u)
  : SucCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : LimSuc u a
  obtain ⟨k, hk⟩ := ha (ε/2) (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε / 2
  use k
  -- ⊢ ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ k
  -- q : ℕ
  -- hq : q ≥ k
  -- ⊢ |u p - u q| < ε
  have h1 : |u p - a| < ε / 2 := hk p hp
  have h2 : |u q - a| < ε / 2 := hk q hq
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a| + |a - u q|   := abs_add_le _ _
     _ = |u p - a| + |u q - a|   := by simp [abs_sub_comm]
     _ < ε / 2 + ε / 2           := by gcongr
     _ = ε                       := by ring

-- 4ª demostración
-- ===============

example
  (h : SucConvergente u)
  : SucCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : LimSuc u a
  obtain ⟨k, hk⟩ := ha (ε/2) (half_pos hε)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε / 2
  use k
  -- ⊢ ∀ p ≥ k, ∀ q ≥ k, |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ k
  -- q : ℕ
  -- hq : q ≥ k
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| :=
           congrArg abs (sub_add_sub_cancel (u p) a (u q)).symm
     _ ≤ |u p - a|  + |a - u q| :=
           abs_add_le (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a| :=
           congrArg (|u p - a| + ·) (abs_sub_comm a (u q))
     _ < ε / 2 + ε / 2 :=
           add_lt_add (hk p hp) (hk q hq)
     _ = ε :=
           add_halves ε

-- Lemas usados
-- ============

variable (a b c d : ℝ)
variable (f : ℝ → ℝ)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (abs_sub_comm a b : |a - b| = |b - a|)
#check (add_halves a : a / 2 + a / 2 = a)
#check (add_left_cancel_iff : a + b = a + c ↔ b = c)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (congrArg f : a = b → f a = f b)
#check (half_pos : 0 < a → 0 < a / 2)
#check (sub_add_sub_cancel a b c : (a - b) + (b - c) = a - c)
