-- Producto_de_funciones_impares.lean
-- El producto de dos funciones impares es par
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que el producto de dos funciones impares es par.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f y g son funciones impares. Tenemos que demostrar que
-- f·g es par; es decir, que
--    (∀ x ∈ ℝ) (f·g)(x) = (f·g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f·g) x = f(x)g(x)
--            = (-f(-x))g(x)      [porque f es impar]
--            = (-f(-x)(-g(-x))   [porque g es impar]
--            = f(-x)g(-x))
--            = (f·g)(-x)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- (esPar f) expresa que f es par.
def esPar (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

-- (esImpar f) expresa que f es impar.
def esImpar  (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = - f (-x)

-- 1ª demostración
example
  (h1 : esImpar f)
  (h2 : esImpar g)
  : esPar (f * g) :=
by
  intro x
  have h1 : f x = -f (-x) := h1 x
  have h2 : g x = -g (-x) := h2 x
  calc (f * g) x
       = f x * g x             := rfl
     _ = (-f (-x)) * g x       := congrArg (. * g x) h1
     _ = (-f (-x)) * (-g (-x)) := congrArg ((-f (-x)) * .) h2
     _ = f (-x) * g (-x)       := neg_mul_neg (f (-x)) (g (-x))
     _ = (f * g) (-x)          := rfl

-- 2ª demostración
example
  (h1 : esImpar f)
  (h2 : esImpar g)
  : esPar (f * g) :=
by
  intro x
  calc (f * g) x
       = f x * g x             := rfl
     _ = (-f (-x)) * g x       := congrArg (. * g x) (h1 x)
     _ = (-f (-x)) * (-g (-x)) := congrArg ((-f (-x)) * .) (h2 x)
     _ = f (-x) * g (-x)       := neg_mul_neg (f (-x)) (g (-x))
     _ = (f * g) (-x)          := rfl

-- 3ª demostración
example
  (h1 : esImpar f)
  (h2 : esImpar g)
  : esPar (f * g) :=
by
  intro x
  calc (f * g) x
       = f x * g x         := rfl
     _ = -f (-x) * -g (-x) := by rw [h1, h2]
     _ = f (-x) * g (-x)   := by rw [neg_mul_neg]
     _ = (f * g) (-x)      := rfl

-- 4ª demostración
example
  (h1 : esImpar f)
  (h2 : esImpar g)
  : esPar (f * g) :=
by
  intro x
  calc (f * g) x
       = f x * g x       := rfl
     _ = f (-x) * g (-x) := by rw [h1, h2, neg_mul_neg]
     _ = (f * g) (-x)    := rfl

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (neg_mul_neg a b : -a * -b = a * b)
