-- Demostracion_por_congruencia.lean
-- En ℝ, |a| = |a - b + b|
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    |a| = |a - b + b|
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  : |a| = |a - b + b| :=
by
  congr
  -- a = a - b + b
  ring

-- Comentario: La táctica congr sustituye una conclusión de la forma
-- A = B por las igualdades de sus subtérminos que no no iguales por
-- definición. Por ejemplo, sustituye la conclusión (x * f y = g w * f z)
-- por las conclusiones (x = g w) y (y = z).

-- 2ª demostración
-- ===============

example
  (a b : ℝ)
  : |a| = |a - b + b| :=
by { congr ; ring }

-- 3ª demostración
-- ===============

example
  (a b : ℝ)
  : |a| = |a - b + b| :=
by ring_nf
