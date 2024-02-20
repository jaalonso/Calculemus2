-- Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.lean
-- s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s ∩ (t ∪ u). Entonces se tiene que
--    x ∈ s                                                          (1)
--    x ∈ t ∪ u                                                      (2)
-- La relación (2) da lugar a dos casos.
--
-- Caso 1: Supongamos que x ∈ t. Entonces, por (1), x ∈ s ∩ t y, por
-- tanto, x ∈ (s ∩ t) ∪ (s ∩ u).
--
-- Caso 2: Supongamos que x ∈ u. Entonces, por (1), x ∈ s ∩ u y, por
-- tanto, x ∈ (s ∩ t) ∪ (s ∩ u).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  rcases hx with ⟨hxs, hxtu⟩
  -- hxs : x ∈ s
  -- hxtu : x ∈ t ∪ u
  rcases hxtu with (hxt | hxu)
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- hxt : x ∈ t
      exact hxt
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- ⊢ x ∈ u
      exact hxu

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    exact ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    exact ⟨hxs, hxu⟩

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    exact Or.inl ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    exact Or.inr ⟨hxs, hxu⟩

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intro x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  aesop

-- 5ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw [inter_union_distrib_left]
