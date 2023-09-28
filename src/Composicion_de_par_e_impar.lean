-- Composicion_de_par_e_impar.lean
-- Si f es par y g es impar, entonces (f ∘ g) es par
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es par y g es impar, entonces f ∘ g es par.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f es una función par y g lo es impar. Tenemos que
-- demostrar que (f ∘ g) es par; es decir, que
--    (∀ x ∈ ℝ) (f ∘ g)(x) = (f ∘ g)(-x)
-- Sea x ∈ ℝ. Entonces,
--    (f ∘ g)(x) = f(g(x))
--               = f(-g(-x))    [porque g es impar]
--               = f(g(-x))     [porque f es par]
--               = (f ∘ g)(-x)

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
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
    _  = f (-g (-x))  := congr_arg f (h2 x)
    _  = f (g (-x))   := (h1 (g (-x))).symm
    _  = (f ∘ g) (-x) := rfl

-- 2ª demostración
example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
     _ = f (-g (-x))  := by rw [h2]
     _ = f (g (-x))   := by rw [← h1]
     _ = (f ∘ g) (-x) := rfl

-- 3ª demostración
example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
     _ = f (g (-x))   := by rw [h2, ← h1]
