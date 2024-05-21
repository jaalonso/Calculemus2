-- Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.lean
-- Si `f(x) ≤ f(y) → x ≤ y`, entonces f es inyectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea f una función de ℝ en ℝ tal que
--    ∀ x y, f(x) ≤ f(y) → x ≤ y
-- Demostrar que f es inyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ ℝ tales que
--    f(x) = f(y)                                                    (1)
-- Tenemos que demostrar que x = y.
--
-- De (1), tenemos que
--    f(x) ≤ f(y)
-- y, por la hipótesis,
--    x ≤ y                                                          (2)
--
-- También de (1), tenemos que
--    f(y) ≤ f(x)
-- y, por la hipótesis,
--    y ≤ x                                                          (3)
-- De (2) y (3), tenemos que
--    x = y

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  have h1 : f x ≤ f y := le_of_eq hxy
  have h2 : x ≤ y     := h h1
  have h3 : f y ≤ f x := ge_of_eq hxy
  have h4 : y ≤ x     := h h3
  show x = y
  exact le_antisymm h2 h4

-- 2ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  have h1 : x ≤ y     := h (le_of_eq hxy)
  have h2 : y ≤ x     := h (ge_of_eq hxy)
  show x = y
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  show x = y
  exact le_antisymm (h (le_of_eq hxy)) (h (ge_of_eq hxy))

-- 3ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
fun _ _ hxy ↦ le_antisymm (h hxy.le) (h hxy.ge)

-- 4ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  apply le_antisymm
  . -- ⊢ x ≤ y
    apply h
    -- ⊢ f x ≤ f y
    exact le_of_eq hxy
  . -- ⊢ y ≤ x
    apply h
    -- ⊢ f y ≤ f x
    exact ge_of_eq hxy

-- 5ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  apply le_antisymm
  . -- ⊢ x ≤ y
    exact h (le_of_eq hxy)
  . -- ⊢ y ≤ x
    exact h (ge_of_eq hxy)

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (ge_of_eq : a = b → a ≥ b)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_of_eq : a = b → a ≤ b)
