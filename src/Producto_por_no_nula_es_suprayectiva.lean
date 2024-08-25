-- Producto_por_no_nula_es_suprayectiva.lean
-- Si c ≠ 0, entonces la función (x ↦ cx) es suprayectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si c es un número real no nulo, entonces la función
--    f(x) = c * x
-- es suprayectiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Hay que demostrar que
--    (∀ x ∈ ℝ)(∃ y ∈ ℝ)[cy = x]
-- Sea x ∈ ℝ. Entonces, y = x/c ∈ R y
--    cy = c(x/c)
--       = y

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {c : ℝ}

open Function

-- 1ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x) a = x
  use (x / c)
  -- ⊢ (fun x => c * x) (x / c) = x
  dsimp
  -- ⊢ c * (x / c) = x
  rw [mul_comm]
  -- ⊢ (x / c) * c = x
  exact div_mul_cancel₀ x h

-- 2ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x) a = x
  use (x / c)
  -- ⊢ (fun x => c * x) (x / c) = x
  exact mul_div_cancel₀ x h

-- 3ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
fun x ↦ ⟨x / c, mul_div_cancel₀ x h⟩

-- 4ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
mul_left_surjective₀ h

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (div_mul_cancel a : b ≠ 0 → (a / b) * b = a)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_left_surjective₀ : c ≠ 0 → Surjective (fun x ↦ c * x))
