-- Inyectiva_si_lo_es_la_composicion.lean
-- Si g ∘ f es inyectiva, entonces f es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean f: X → Y y g: Y → Z. Demostrar que si g ∘ f es inyectiva,
-- entonces f es inyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean a, b ∈ X tales que
--    f(a) = f(b)
-- Entonces,
--    g(f(a)) = g(f(b))
-- Luego
--    (g ∘ f)(a) = (g ∘ f)(b)
-- y, como g ∘ f es inyectiva,
--    a = b

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (h : Injective (g ∘ f))
  : Injective f :=
by
  intro a b hab
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  have h1 : (g ∘ f) a = (g ∘ f) b := by simp_all only [comp_apply]
  exact h h1

-- 2ª demostración
-- ===============

example
  (h : Injective (g ∘ f))
  : Injective f :=
by
  intro a b hab
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  apply h
  -- ⊢ (g ∘ f) a = (g ∘ f) b
  change g (f a) = g (f b)
  -- ⊢ g (f a) = g (f b)
  rw [hab]

-- Lemas usados
-- ============

-- variable (x : X)
-- #check (Function.comp_apply : (g ∘ f) x = g (f x))
