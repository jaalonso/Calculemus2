-- Funcion_no_acotada_inferiormente.lean
-- Si para cada a existe un x tal que f(x) < a, entonces f no tiene cota inferior.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es una función de ℝ en ℝ tal que para cada a,
-- existe un x tal que f x < a, entonces f no tiene cota inferior.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f tiene cota inferior. Sea b una de dichas cotas
-- inferiores. Por la hipótesis, existe un x tal que f(x) < b. Además,
-- como b es una cota inferior de f, b ≤ f(x) que contradice la
-- desigualdad anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def acotadaInf (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaInferior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ acotadaInf f :=
by
  intros hf
  -- hf : acotadaInf f
  -- ⊢ False
  cases' hf with b hb
  -- b : ℝ
  -- hb : CotaInferior f b
  cases' h b with x hx
  -- x : ℝ
  -- hx : f x < b
  have : b ≤ f x := hb x
  linarith

-- 2ª demostración
example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ acotadaInf f :=
by
  intros hf
  -- hf : acotadaInf f
  -- ⊢ False
  rcases hf with ⟨b, hb : CotaInferior f b⟩
  rcases h b with ⟨x, hx : f x < b⟩
  have : b ≤ f x := hb x
  linarith
