-- Reto_22.lean
-- Subsucesiones con límites distintos implican no convergencia.
-- Sevilla, 5-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- El reto de esta semana consiste en demostrar en Lean 4 que si
-- una sucesión tiene dos subsucesiones con límites distintos,
-- entonces la sucesión no es convergente. Para ello, completar la
-- siguiente teoría:
--    import Mathlib.Basic.Real.Basic
--    import Mathlib.Tactic
--
--    -- a converge a L
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    -- La sucesión a es convergente
--    def SucConvergente (a : ℕ → ℝ) : Prop :=
--      ∃ L, LimSuc a L
--
--    -- φ es una función de extracción.
--    def extraccion (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    -- b es una subsucesión de a.
--    def subsucesion (b a : ℕ → ℝ) : Prop :=
--      ∃ φ, extraccion φ ∧ b = a ∘ φ
--
--    variable {a b₁ b₂ : ℕ → ℝ}
--    variable {L L₁ L₂ M : ℝ}
--
--    example
--      (hb₁ : subsucesion b₁ a)
--      (hL₁ : LimSuc b₁ L₁)
--      (hb₂ : subsucesion b₂ a)
--      (hL₂ : LimSuc b₂ L₂)
--      (h : L₁ ≠ L₂)
--      : ¬SucConvergente a :=
--    by sorry
-- ---------------------------------------------------------------

module

import Mathlib.Tactic

-- a converge a L
def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- La sucesión a es convergente
def SucConvergente (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

-- φ es una función de extracción.
def extraccion (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

-- b es una subsucesión de a.
def subsucesion (b a : ℕ → ℝ) : Prop :=
  ∃ φ, extraccion φ ∧ b = a ∘ φ

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ M : ℝ}

lemma unicidad_limite -- del Reto 9
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  set ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  calc ε = |(L - a k) + (a k - M)| := by grind
       _ < ε                       := by grind

lemma limite_subsucesion -- del Reto 21
  (hb : subsucesion b a)
  (hL : LimSuc a L)
  : LimSuc b L :=
by
  obtain ⟨φ, hφ, rfl⟩ := hb
  -- φ : ℕ → ℕ
  -- hφ : extraccion φ
  -- ⊢ LimSuc (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := hL ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  exact ⟨k, fun n hn ↦ hk (φ n) (le_trans hn hφ.le_apply)⟩

-- 1ª demostración
-- ===============

example
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  intro h1
  -- h1 : SucConvergente a
  -- ⊢ False
  apply h
  -- ⊢ L₁ = L₂
  obtain ⟨L, hL⟩ := h1
  -- L : ℝ
  -- hL : LimSuc a L
  have h2 : LimSuc b₁ L := limite_subsucesion hb₁ hL
  have h3 : LimSuc b₂ L := limite_subsucesion hb₂ hL
  calc L₁
       = L  := unicidad_limite hL₁ h2
     _ = L₂ := unicidad_limite h3 hL₂

-- 2ª demostración
-- ===============

example
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  exact h (Trans.trans
           (unicidad_limite hL₁ (limite_subsucesion hb₁ hL))
           (unicidad_limite (limite_subsucesion hb₂ hL) hL₂))

-- 3ª demostración
-- ===============

theorem no_convergencia_subsucesiones
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  exact h ((unicidad_limite hL₁ (limite_subsucesion hb₁ hL)).trans
           (unicidad_limite (limite_subsucesion hb₂ hL) hL₂))
