-- Suma_constante_es_suprayectiva.lean
-- La función (x ↦ x + c) es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para todo número real c, la función
--    f(x) = x + c
-- es suprayectiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x ∈ ℝ)(∃ y ∈ ℝ)[y+c = x]
-- Sea x ∈ ℝ. Entonces, y = x-c ∈ ℝ y
--    y + c = (x - c) + c
--          = x

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {c : ℝ}

open Function

-- 1ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  dsimp
  -- ⊢ (x - c) + c = x
  exact sub_add_cancel x c

-- 2ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  change (x - c) + c = x
  -- ⊢ (x - c) + c = x
  exact sub_add_cancel x c

-- 3ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  exact sub_add_cancel x c

-- 4ª demostración
example : Surjective (fun x ↦ x + c) :=
fun x ↦ ⟨x - c, sub_add_cancel x c⟩

-- 5ª demostración
example : Surjective (fun x ↦ x + c) :=
fun x ↦ ⟨x - c, by ring⟩

-- 6ª demostración
example : Surjective (fun x ↦ x + c) :=
add_right_surjective c

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (sub_add_cancel a b : (a - b) + b = a)
-- #check (add_right_surjective c : Surjective (fun x ↦ x + c))
