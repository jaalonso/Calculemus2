-- Imagen_de_la_diferencia_de_conjuntos.lean
-- f[s] \ f[t] ⊆ f[s \ t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' s \ f '' t ⊆ f '' (s \ t)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s] \ f[t]. Entonces,
--    y ∈ f[s]                                                       (1)
--    y ∉ f[t]                                                       (2)
-- Por (1), existe un x tal que
--    x ∈ s                                                          (3)
--    f(x) = y                                                       (4)
-- Por tanto, para demostrar que y ∈ f[s \ t], basta probar que
-- x ∉ t. Para ello, supongamos que x ∈ t. Entonces, por (4),
-- y ∈ f[t] en contradicción con (2).

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

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  have h1 : x ∉ t := by
    intro xt
    -- xt : x ∈ t
    -- ⊢ False
    have h2 : f x ∈ f '' t := mem_image_of_mem f xt
    have h3 : y ∈ f '' t := by rwa [fxy] at h2
    show False
    exact ynft h3
  have h4 : x ∈ s \ t := mem_diff_of_mem xs h1
  have h5 : f x ∈ f '' (s \ t) := mem_image_of_mem f h4
  show y ∈ f '' (s \ t)
  rwa [fxy] at h5

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply ynft
      -- ⊢ y ∈ f '' t
      rw [←fxy]
      -- ⊢ f x ∈ f '' t
      apply mem_image_of_mem
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  rintro y ⟨⟨x, xs, fxy⟩, ynft⟩
  -- y : β
  -- ynft : ¬y ∈ f '' t
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (s \ t)
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  aesop

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
fun y ⟨⟨x, xs, fxy⟩, ynft⟩ ↦ ⟨x, by aesop⟩

-- 5ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t

-- Lemmas usados
-- =============

-- variable (x : α)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
-- #check (subset_image_diff f s t : f '' s \ f '' t ⊆ f '' (s \ t))
