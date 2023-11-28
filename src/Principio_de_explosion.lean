-- Principio_de_explosion.lean
-- Si 0 < 0, entonces a > 37 para cualquier número a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si 0 < 0, entonces a > 37 para cualquier número a.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Basta demostrar una cotradicción, ya que de una contradicción se
-- sigue cualquier cosa.
--
-- La hipótesis es una contradicción con la propiedad irreflexiva de la
-- relación <.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable (a : ℕ)

-- 1ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  exfalso
  -- ⊢ False
  show False
  exact lt_irrefl 0 h

-- Comentario: La táctica exfalso sustituye el objetivo por false.

-- 2ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  exfalso
  -- ⊢ False
  apply lt_irrefl 0 h

-- 3ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
absurd h (lt_irrefl 0)

-- 4ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  have : ¬ 0 < 0 :=  lt_irrefl 0
  contradiction

-- Comentario: La táctica contradiction busca dos hipótesis
-- contradictorias.

-- 5ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by linarith

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- #check (lt_irrefl a : ¬a < a)
-- #check (absurd : p → ¬p → q)
