-- Propiedad_de_monotonia_de_la_interseccion.lean
-- Si s ⊆ t, entonces s ∩ u ⊆ t ∩ u.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s ∩ u. Entonces, se tiene que
--   x ∈ s                                                           (1)
--   x ∈ u                                                           (2)
-- De (1) y s ⊆ t, se tiene que
--   x ∈ t                                                           (3)
-- De (3) y (2) se tiene que
--   x ∈ t ∩ u
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rw [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  intros x h1
  -- x : α
  -- h1 : x ∈ s ∩ u
  -- ⊢ x ∈ t ∩ u
  rcases h1 with ⟨xs, xu⟩
  -- xs : x ∈ s
  -- xu : x ∈ u
  constructor
  . -- ⊢ x ∈ t
    rw [subset_def] at h
    -- h : ∀ (x : α), x ∈ s → x ∈ t
    apply h
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ u
    exact xu

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rw [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  rintro x ⟨xs, xu⟩
  -- x : α
  -- xs : x ∈ s
  -- xu : x ∈ u
  rw [subset_def] at h
  -- h : ∀ (x : α), x ∈ s → x ∈ t
  exact ⟨h x xs, xu⟩

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  simp only [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  rintro x ⟨xs, xu⟩
  -- x : α
  -- xs : x ∈ s
  -- xu : x ∈ u
  rw [subset_def] at h
  -- h : ∀ (x : α), x ∈ s → x ∈ t
  exact ⟨h _ xs, xu⟩

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  intros x xsu
  -- x : α
  -- xsu : x ∈ s ∩ u
  -- ⊢ x ∈ t ∩ u
  exact ⟨h xsu.1, xsu.2⟩

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rintro x ⟨xs, xu⟩
  -- xs : x ∈ s
  -- xu : x ∈ u
  -- ⊢ x ∈ t ∩ u
  exact ⟨h xs, xu⟩

-- 6ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦  ⟨h xs, xu⟩

-- 7ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter_left u h

-- Lema usado
-- ==========

-- #check (inter_subset_inter_left u : s ⊆ t → s ∩ u ⊆ t ∩ u)
