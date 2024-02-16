-- El_limite_de_u_es_a_syss_el_de_u-a_es_0.lean
-- El límite de uₙ es a syss el de uₙ-a es 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que el límite de uₙ es a si y solo si el de uₙ-a es 0.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se prueba por la siguiente cadena de equivalencias
--    limite u a ↔ (∀ε>0)(∃N)(∀n≥N)[|u(n) - a| < ε]
--               ↔ (∀ε>0)(∃N)(∀n≥N)[|(u(n) - a) - 0| < ε]
--               ↔ limite (fun n ↦ u(n) - a) 0

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  {u : ℕ → ℝ}
variable {a c x : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
 fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  : limite u a ↔ limite (fun i ↦ u i - a) 0 :=
by
  rw [iff_eq_eq]
  calc limite u a
       = ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε       := rfl
     _ = ∀ ε > 0, ∃ N, ∀ n ≥ N, |(u n - a) - 0| < ε := by simp
     _ = limite (fun i ↦ u i - a) 0                 := rfl

-- 2ª demostración
-- ===============

example
  : limite u a ↔ limite (fun i ↦ u i - a) 0 :=
by
  constructor
  . -- ⊢ limite u a → limite (fun i => u i - a) 0
    intros h ε hε
    -- h : limite u a
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i - a) n - 0| < ε
    convert h ε hε using 2
    -- x : ℕ
    -- ⊢ (∀ (n : ℕ), n ≥ x → |(fun i => u i - a) n - 0| < ε) ↔ ∀ (n : ℕ), n ≥ x → |u n - a| < ε
    norm_num
  . -- ⊢ limite (fun i => u i - a) 0 → limite u a
    intros h ε hε
    -- h : limite (fun i => u i - a) 0
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
    convert h ε hε using 2
    -- x : ℕ
    -- ⊢ (∀ (n : ℕ), n ≥ x → |u n - a| < ε) ↔ ∀ (n : ℕ), n ≥ x → |(fun i => u i - a) n - 0| < ε
    norm_num

-- 3ª demostración
-- ===============

example
  : limite u a ↔ limite (fun i ↦ u i - a) 0 :=
by
  constructor <;>
  { intros h ε hε
    convert h ε hε using 2
    norm_num }

-- 4ª demostración
-- ===============

lemma limite_con_suma
  (c : ℝ)
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
  fun ε hε ↦ (by convert h ε hε using 2; norm_num)

lemma CNS_limite_con_suma
  (c : ℝ)
  : limite u a ↔ limite (fun i ↦ u i + c) (a + c) :=
by
  constructor
  . -- ⊢ limite u a → limite (fun i => u i + c) (a + c)
    apply limite_con_suma
  . -- ⊢ limite (fun i => u i + c) (a + c) → limite u a
    intro h
    -- h : limite (fun i => u i + c) (a + c)
    -- ⊢ limite u a
    convert limite_con_suma (-c) h using 2
    . -- ⊢ u x = u x + c + -c
      simp
    . -- ⊢ a = a + c + -c
      simp

example
  (u : ℕ → ℝ)
  (a : ℝ)
  : limite u a ↔ limite (fun i ↦ u i - a) 0 :=
by
  convert CNS_limite_con_suma (-a) using 2
  -- ⊢ 0 = a + -a
  simp

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- #check (iff_eq_eq : (p ↔ q) = (p = q))
