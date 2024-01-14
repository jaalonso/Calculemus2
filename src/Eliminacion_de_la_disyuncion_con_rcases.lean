-- Eliminacion_de_la_disyuncion_con_rcases.lean
-- En ℝ, si x ≠ 0 entonces x < 0 ó x > 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Sea x un número real. Demostrar que si
--    x ≠ 0
-- entonces
--    x < 0 ∨ x > 0
 -- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usando el siguiente lema
--    (∀ x y ∈ ℝ)[x < y ∨ x = y ∨ y < x]
-- se demuestra distinguiendo tres casos.
--
-- Caso 1: Supongamos que x < 0. Entonces, se verifica la disyunción ya
-- que se verifica su primera parte.
--
-- Caso 2: Supongamos que x = 0. Entonces, se tiene una contradicción
-- con la hipótesis.
--
-- Caso 3: Supongamos que x > 0. Entonces, se verifica la disyunción ya
-- que se verifica su segunda parte.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {x : ℝ}

-- 1ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
by
  rcases lt_trichotomy x 0 with hx1 | hx2 | hx3
  . -- hx1 : x < 0
    left
    -- ⊢ x < 0
    exact hx1
  . -- hx2 : x = 0
    contradiction
  . -- hx3 : 0 < x
    right
    -- ⊢ x > 0
    exact hx3

-- 2ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
Ne.lt_or_lt h

-- 3ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
by aesop

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (lt_trichotomy x y : x < y ∨ x = y ∨ y < x)
