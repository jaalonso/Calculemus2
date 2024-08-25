-- Producto_por_no_nula_y_suma_es_suprayectiva.lean
-- Si c ≠ 0, entonces la función (x ↦ cx + d) es suprayectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si c es un número real no nulo, entonces la función
--    f(x) = c * x + d
-- es suprayectiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Hay que demostrar que
--    (∀x ∈ ℝ)(∃y ∈ ℝ)[cy+d = x]
-- Sea x ∈ ℝ. Entonces, y = (x-d)/c ∈ R y
--    cy = c((x-d)/c)+d
--       = (x-d)+d
--       = x

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {c d : ℝ}

open Function

-- 1ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  dsimp
  -- ⊢ c * ((x - d) / c) + d = x
  show c * ((x - d) / c) + d = x
  calc c * ((x - d) / c) + d
         = (x - d) + d := congrArg (. + d) (mul_div_cancel₀ (x - d) h)
       _ = x           := sub_add_cancel x d

-- 2ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  dsimp
  -- ⊢ c * ((x - d) / c) + d = x
  simp [mul_div_cancel₀, h]

-- 3ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  simp [mul_div_cancel₀, h]

-- 4ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
fun x ↦ ⟨(x - d) / c, by simp [mul_div_cancel₀, h]⟩

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (sub_add_cancel a b : a - b + b = a)
