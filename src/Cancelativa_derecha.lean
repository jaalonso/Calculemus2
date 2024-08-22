-- Cancelativa_derecha.lean
-- Si R es un anillo y a, b, c ∈ R tales que a+b=c+b, entonces a=c
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b, c ∈ R tales que
--    a + b = c + b
-- entonces
--    a = c
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    a = a + 0           [por suma con cero]
--      = a + (b + -b)    [por suma con opuesto]
--      = (a + b) + -b    [por asociativa]
--      = (c + b) + -b    [por hipótesis]
--      = c + (b + -b)    [por asociativa]
--      = c + 0           [por suma con opuesto]
--      = c               [por suma con cero]

-- 2ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    a = (a + b) + -b
--      = (c + b) + -b    [por hipótesis]
--      = c

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

-- 1ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
calc
  a = a + 0        := by rw [add_zero]
  _ = a + (b + -b) := by rw [add_neg_cancel]
  _ = (a + b) + -b := by rw [add_assoc]
  _ = (c + b) + -b := by rw [h]
  _ = c + (b + -b) := by rw [← add_assoc]
  _ = c + 0        := by rw [← add_neg_cancel]
  _ = c            := by rw [add_zero]

-- 2ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
calc
  a = (a + b) + -b := (add_neg_cancel_right a b).symm
  _ = (c + b) + -b := by rw [h]
  _ = c            := add_neg_cancel_right c b

-- 3ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← add_neg_cancel_right a b]
  rw [h]
  rw [add_neg_cancel_right]

-- 4ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

-- 5ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
add_right_cancel h

-- Lemas usados
-- ============

-- #check (add_assoc a b c : (a + b) + c = a + (b + c))
-- #check (add_neg_cancel a : a + -a = 0)
-- #check (add_neg_cancel_right a b : (a + b) + -b = a)
-- #check (add_right_cancel : a + b = c + b → a = c)
-- #check (add_zero a :  a + 0 = a)
