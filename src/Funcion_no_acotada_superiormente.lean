-- Funcion_no_acotada_superiormente.lean
-- Si para cada a existe un x tal que f(x) > a, entonces f no tiene cota superior.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es una función de ℝ en ℝ tal que para cada a,
-- existe un x tal que f x > a, entonces f no tiene cota superior.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f tiene cota superior. Sea b una de dichas cotas
-- superiores. Por la hipótesis, existe un x tal que f(x) > b. Además,
-- como b es una cota superior de f, f(x) ≤ b que contradice la
-- desigualdad anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ a, ∃ x, f x > a)
  : ¬ acotadaSup f :=
by
  intros hf
  -- hf : acotadaSup f
  -- ⊢ False
  cases' hf with b hb
  -- b : ℝ
  -- hb : CotaSuperior f b
  cases' h b with x hx
  -- x : ℝ
  -- hx : f x > b
  have : f x ≤ b := hb x
  linarith

-- 2ª demostración
theorem sinCotaSup
  (h : ∀ a, ∃ x, f x > a)
  : ¬ acotadaSup f :=
by
  intros hf
  -- hf : acotadaSup f
  -- ⊢ False
  rcases hf with ⟨b, hb : CotaSuperior f b⟩
  rcases h b with ⟨x, hx : f x > b⟩
  have : f x ≤ b := hb x
  linarith
