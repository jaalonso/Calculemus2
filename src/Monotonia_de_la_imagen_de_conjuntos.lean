-- Monotonia_de_la_imagen_de_conjuntos.lean
-- Si s ⊆ t, entonces f[s] ⊆ f[t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si s ⊆ t, entonces
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s]. Entonces, existe un x tal que
--    x ∈ s                                                          (1)
--    f(x) = y                                                       (2)
-- Por (1) y la hipótesis,
--    x ∈ t                                                          (3)
-- Por (3),
--    f(x) ∈ f[t]                                                    (4)
-- y, por (2) y (4),
--    y ∈ f[t]

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

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rw [mem_image] at hy
  -- hy : ∃ x, x ∈ s ∧ f x = y
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ t
    exact h xs
  . -- ⊢ f x = y
    exact fxy

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rcases hy with ⟨x, xs, fxy⟩
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  exact ⟨h xs, fxy⟩

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h

-- Lemas usados
-- ============

-- variable (y : β)
-- #check (mem_image f s y : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y)
-- #check (image_subset f : s ⊆ t → f '' s ⊆ f '' t)
