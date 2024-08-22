-- Producto_de_funciones_no_negativas.lean
-- El producto de funciones no negativas es no negativo
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que el producto de dos funciones no negativas es no
-- negativa.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b
--
-- Hay que demostrar que
--    (∀ x ∈ ℝ) [0 ≤ f(x) * g(x)]                                      (1)
-- Para ello, sea x ∈ R. Puesto que f es no negatica, se tiene que
--    0 ≤ f(x)                                                         (2)
-- y, puesto que g es no negativa, se tiene que
--    0 ≤ g(x)                                                         (3)
-- De (2) y (3), por mul_nonneg, se tiene que
--    0 ≤ f(x) * g(x)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)

-- 1ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x := by
  { intro x
    have h2: 0 ≤ f x := nnf x
    have h3: 0 ≤ g x := nng x
    show 0 ≤ f x * g x
    exact mul_nonneg h2 h3 }
  show CotaInferior (f * g) 0
  exact h1

-- 2ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x := by
  { intro x
    show 0 ≤ f x * g x
    exact mul_nonneg (nnf x) (nng x) }
  show CotaInferior (f * g) 0
  exact h1

-- 3ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  intro x
  dsimp
  apply mul_nonneg
  . apply nnf
  . apply nng

-- 4ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
λ x ↦ mul_nonneg (nnf x) (nng x)

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
