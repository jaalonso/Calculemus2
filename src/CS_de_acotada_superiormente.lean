-- CS_de_acotada_superiormente.lean
-- Si ¬(∀a)(∃x)[f(x) > a]​, entonces f está acotada superiormente.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si ¬(∀a)(∃x)[f(x) > a]​, entonces f está acotada
-- superiormente.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que f es acotada superiormente; es decir, que
--    (∃a)(∀x)[f(x) ≤ a]
-- que es exactamente la fórmula obtenida interiorizando la negación en
-- la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  unfold acotadaSup
  -- ⊢ ∃ a, CotaSuperior f a
  unfold CotaSuperior
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 2ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  unfold acotadaSup CotaSuperior
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 3ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h
