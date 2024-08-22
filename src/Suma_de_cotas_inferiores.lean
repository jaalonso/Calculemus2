-- Suma_de_cotas_inferiores.lean
-- La suma de una cota inferior de f y una cota inferior de g es una
--   cota inferior de f+g
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de una cota inferior de f y una  cota inferior
-- de g es una cota inferior de f + g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Por la definición de cota inferior, hay que demostrar que
--    (∀ x ∈ ℝ) [a + b ≤ f(x) + g(x)]                                  (1)
-- Para ello, sea x ∈ R. Puesto que es a es una cota inferior de f, se
-- tiene que
--    a ≤ f(x)                                                         (2)
-- y, puesto que b es una cota inferior de g, se tiene que
--    b ≤ g(x)                                                         (3)
-- De (2) y (3), por add_le_add, se tiene que
--    a + b ≤ f(x) + g(x)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable {f g : ℝ → ℝ}
variable {a b : ℝ}

-- 1ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x := by
  { intro x
    have h1a : a ≤ f x := hfa x
    have h1b : b ≤ g x := hgb x
    show a + b ≤ f x + g x
    exact add_le_add h1a h1b }
  show CotaInferior (f + g) (a + b)
  exact h1

-- 2ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x := by
  { intro x
    show a + b ≤ f x + g x
    exact add_le_add (hfa x) (hgb x) }
  show CotaInferior (f + g) (a + b)
  exact h1

-- 3ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  . apply hfa
  . apply hgb

-- 4ª demostración
theorem sumaCotaInf
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
