-- Demostracion_por_extensionalidad.lean
-- Las funciones f(x,y) = (x + y)² y g(x,y) = x² + 2xy + y² son iguales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2)
-- ----------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
-- ===============

example : (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2) :=
by
  ext u v
  -- u v : ℝ
  -- ⊢ (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2
  ring

-- Comentario: La táctica ext transforma las conclusiones de la forma
-- (fun x ↦ f x) = (fun x ↦ g x) en f x = g x.

-- 2ª demostración
-- ===============

example : (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2) :=
by { ext ; ring }
