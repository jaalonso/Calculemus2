-- Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.lean
-- (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ (s ∩ t) ∪ (s ∩ u). Entonces son posibles dos casos.
--
-- 1º caso: Supongamos que x ∈ s ∩ t. Entonces, x ∈ s y x ∈ t (y, por
-- tanto, x ∈ t ∪ u). Luego, x ∈ s ∩ (t ∪ u).
--
-- 2º caso: Supongamos que x ∈ s ∩ u. Entonces, x ∈ s y x ∈ u (y, por
-- tanto, x ∈ t ∪ u). Luego, x ∈ s ∩ (t ∪ u).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ t ∪ s ∩ u
  -- ⊢ x ∈ s ∩ (t ∪ u)
  rcases hx with (xst | xsu)
  . -- xst : x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xst.2
  . -- xsu : x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact xsu.1
    . -- ⊢ x ∈ t ∪ u
      right
      -- ⊢ x ∈ u
      exact xsu.2

-- 2ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . -- x : α
    -- xs : x ∈ s
    -- xt : x ∈ t
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    left
    -- ⊢ x ∈ t
    exact xt
  . -- x : α
    -- xs : x ∈ s
    -- xu : x ∈ u
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 3ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by rw [inter_union_distrib_left s t u]

-- 4ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ t ∪ s ∩ u
  -- ⊢ x ∈ s ∩ (t ∪ u)
  aesop
