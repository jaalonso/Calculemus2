-- Suprayectiva_si_lo_es_la_composicion.lean
-- Si g ∘ f es suprayectiva, entonces g es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean f: X → Y y g: Y → Z. Demostrar que si g ∘ f es suprayectiva,
-- entonces g es suprayectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se z ∈ Z. Entonces, por ser g ∘ f suprayectiva, existe un x ∈ X tal
-- que
--    (g ∘ f)(x) = z                                                 (1)
-- Por tanto, existe y = f(x) ∈ Y tal que
--    g(y) = g(f(x))
--         = (g ∘ f)(x)
--         = z             [por (1)]

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
  (h : Surjective (g ∘ f))
  : Surjective g :=
by
  intro z
  -- z : Z
  -- ⊢ ∃ a, g a = z
  cases' h z with x hx
  -- x : X
  -- hx : (g ∘ f) x = z
  use f x
  -- ⊢ g (f x) = z
  exact hx

-- 2ª demostración
-- ===============

example
  (h : Surjective (g ∘ f))
  : Surjective g :=
by
  intro z
  -- z : Z
  -- ⊢ ∃ a, g a = z
  cases' h z with x hx
  -- x : X
  -- hx : (g ∘ f) x = z
  exact ⟨f x, hx⟩
