-- Imagen_de_la_interseccion.lean
-- f[s ∩ t] ⊆ f[s] ∩ f[t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' (s ∩ t) ⊆ f '' s ∩ f '' t
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea tal que
--    y ∈ f[s ∩ t]
-- Por tanto, existe un x tal que
--   x ∈ s ∩ t                                                       (1)
--   f(x) = y                                                        (2)
-- Por (1), se tiene que
--   x ∈ s                                                           (3)
--   x ∈ t                                                           (4)
-- Por (2) y (3), se tiene
--   y ∈ f[s]                                                        (5)
-- Por (2) y (4), se tiene
--   y ∈ f[t]                                                        (6)
-- Por (5) y (6), se tiene
--   y ∈ f[s] ∩ f[t]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∩ t ∧ f x = y
  rcases hx with ⟨xst, fxy⟩
  -- xst : x ∈ s ∩ t
  -- fxy : f x = y
  constructor
  . -- ⊢ y ∈ f '' s
    use x
    -- ⊢ x ∈ s ∧ f x = y
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' t
    use x
    -- ⊢ x ∈ t ∧ f x = y
    constructor
    . -- ⊢ x ∈ t
      exact xst.2
    . -- ⊢ f x = y
      exact fxy

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- xs : x ∈ s
  -- xt : x ∈ t
  constructor
  . -- ⊢ y ∈ f '' s
    use x
  . -- ⊢ y ∈ f '' t
    use x

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; aesop

-- Lemas usados
-- ============

-- #check (image_inter_subset f s t : f '' (s ∩ t) ⊆ f '' s ∩ f '' t)
