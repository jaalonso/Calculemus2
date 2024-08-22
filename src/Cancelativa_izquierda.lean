-- Cancelativa_izquierda.lean
-- Si R es un anillo y a, b, c ∈ R tales que a+b=a+c, entonces b=c
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b, c ∈ R tales que
--    a + b = a + c
-- entonces
--    b = c
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- ======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    b = 0 + b           [por suma con cero]
--      = (-a + a) + b    [por suma con opuesto]
--      = -a + (a + b)    [por asociativa]
--      = -a + (a + c)    [por hipótesis]
--      = (-a + a) + c    [por asociativa]
--      = 0 + c           [por suma con opuesto]
--      = c               [por suma con cero]

-- 2ª demostración en LN
-- =====================

-- Por la siguiente cadena de implicaciones
--    a + b = a + c
--    ==> -a + (a + b) = -a + (a + c)     [sumando -a]
--    ==>  (-a + a) + b = (-a + a) + c    [por la asociativa]
--    ==>  0 + b = 0 + b                  [suma con opuesto]
--    ==>  b = c                          [suma con cero]

-- 3ª demostración en LN
-- =====================

-- Por la siguiente cadena de igualdades
--    b = -a + (a + b)
--      = -a + (a + c)   [por la hipótesis]
--      = c

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

-- 1ª demostración
example
  (h : a + b = a + c)
  : b = c :=
calc
  b = 0 + b        := by rw [zero_add]
  _ = (-a + a) + b := by rw [neg_add_cancel]
  _ = -a + (a + b) := by rw [add_assoc]
  _ = -a + (a + c) := by rw [h]
  _ = (-a + a) + c := by rw [←add_assoc]
  _ = 0 + c        := by rw [neg_add_cancel]
  _ = c            := by rw [zero_add]

-- 2ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  have h1 : -a + (a + b) = -a + (a + c) :=
    congrArg (HAdd.hAdd (-a)) h
  clear h
  rw [← add_assoc] at h1
  rw [neg_add_cancel] at h1
  rw [zero_add] at h1
  rw [← add_assoc] at h1
  rw [neg_add_cancel] at h1
  rw [zero_add] at h1
  exact h1

-- 3ª demostración
example
  (h : a + b = a + c)
  : b = c :=
calc
  b = -a + (a + b) := by rw [neg_add_cancel_left a b]
  _ = -a + (a + c) := by rw [h]
  _ = c            := by rw [neg_add_cancel_left]

-- 4ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b]
  rw [h]
  rw [neg_add_cancel_left]

-- 5ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

-- 6ª demostración
example
  (h : a + b = a + c)
  : b = c :=
add_left_cancel h

-- Lemas usados
-- ============

-- #check (add_assoc a b c : (a + b) + c = a + (b + c))
-- #check (add_left_cancel : a + b = a + c → b = c)
-- #check (neg_add_cancel a : -a + a = 0)
-- #check (neg_add_cancel_left a b : -a + (a + b) = b)
-- #check (zero_add a :  0 + a = a)
