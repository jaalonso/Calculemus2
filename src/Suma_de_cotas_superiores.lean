-- Suma_de_cotas_superiores.lean
-- La suma de una cota superior de f y una cota superior de g es una
--   cota superior de f+g
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de una cota superior de f y una cota superior
-- de g es una cota superior de f + g.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Por la definición de cota superior, hay que demostrar que
--    (∀ x ∈ ℝ) [f(x) + g(x) ≤ a + b]                                  (1)
-- Para ello, sea x ∈ R. Puesto que es a es una cota superior de f, se
-- tiene que
--    f(x) ≤ a                                                         (2)
-- y, puesto que b es una cota superior de g, se tiene que
--    g(x) ≤ b                                                         (3)
-- De (2) y (3), por add_le_add, se tiene que
--    f(x) + g(x) ≤ a + b
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

variable {f g : ℝ → ℝ}
variable {a b : ℝ}

-- 1ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  have h1 : ∀ x, (f + g) x  ≤ a + b := by
  { intro x
    have h2 : f x ≤ a := hfa x
    have h3 : g x ≤ b := hgb x
    show (f + g) x ≤ a + b
    exact add_le_add h2 h3 }
  show CotaSuperior (f + g) (a + b)
  exact h1

-- 2ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  have h1 : ∀ x, (f + g) x ≤ a + b := by
  { intro x
    show (f + g) x ≤ a + b
    exact add_le_add (hfa x) (hgb x) }
  show CotaSuperior (f + g) (a + b)
  exact h1

-- 3ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  . apply hfa
  . apply hgb

-- 4ª demostración
-- ===============

theorem sumaCotaSup
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
