-- Imagen_de_la_interseccion_general.lean
-- Imagen de la intersección general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f[⋂ᵢ Aᵢ] ⊆ ⋂ᵢ f[Aᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y tal que
--    y ∈ f[⋂ᵢ Aᵢ]                                                   (1)
-- Tenemos que demostrar que y ∈ ⋂ᵢ f[Aᵢ]. Para ello, sea i ∈ I, tenemos
-- que demostrar que y ∈ f[Aᵢ].
--
-- Por (1), existe un x tal que
--    x ∈ ⋂ᵢ Aᵢ                                                      (2)
--    f(x) = y                                                       (3)
-- Por (2),
--    x ∈ Aᵢ
-- y, por tanto,
--    f(x) ∈ f[Aᵢ]
-- que, junto con (3), da que
--    y ∈ f[Aᵢ]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)

-- 1ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  have h1 : ∃ x, x ∈ ⋂ i, A i ∧ f x = y := (mem_image f (⋂ i, A i) y).mp h
  obtain ⟨x, hx : x ∈ ⋂ i, A i ∧ f x = y⟩ := h1
  have h2 : x ∈ ⋂ i, A i := hx.1
  have h3 : f x = y := hx.2
  have h4 : ∀ i, y ∈ f '' A i := by
    intro i
    have h4a : x ∈ A i := mem_iInter.mp h2 i
    have h4b : f x ∈ f '' A i := mem_image_of_mem f h4a
    show y ∈ f '' A i
    rwa [h3] at h4b
  show y ∈ ⋂ i, f '' A i
  exact mem_iInter.mpr h4

-- 1ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  apply mem_iInter_of_mem
  -- ⊢ ∀ (i : I), y ∈ f '' A i
  intro i
  -- i : I
  -- ⊢ y ∈ f '' A i
  cases' h with x hx
  -- x : α
  -- hx : x ∈ ⋂ (i : I), A i ∧ f x = y
  cases' hx with xIA fxy
  -- xIA : x ∈ ⋂ (i : I), A i
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ f '' A i
  apply mem_image_of_mem
  -- ⊢ x ∈ A i
  exact mem_iInter.mp xIA i

-- 2ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' ⋂ (i : I), A i
  -- ⊢ y ∈ ⋂ (i : I), f '' A i
  apply mem_iInter_of_mem
  -- ⊢ ∀ (i : I), y ∈ f '' A i
  intro i
  -- i : I
  -- ⊢ y ∈ f '' A i
  rcases h with ⟨x, xIA, rfl⟩
  -- x : α
  -- xIA : x ∈ ⋂ (i : I), A i
  -- ⊢ f x ∈ f '' A i
  exact mem_image_of_mem f (mem_iInter.mp xIA i)

-- 3ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by
  intro y
  -- y : β
  -- ⊢ y ∈ f '' ⋂ (i : I), A i → y ∈ ⋂ (i : I), f '' A i
  simp
  -- ⊢ ∀ (x : α), (∀ (i : I), x ∈ A i) → f x = y → ∀ (i : I), ∃ x, x ∈ A i ∧ f x = y
  intros x xIA fxy i
  -- x : α
  -- xIA : ∀ (i : I), x ∈ A i
  -- fxy : f x = y
  -- i : I
  -- ⊢ ∃ x, x ∈ A i ∧ f x = y
  use x, xIA i

-- 4ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
image_iInter_subset A f

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set α)
-- #check (image_iInter_subset A f : f '' ⋂ i, A i ⊆ ⋂ i, f '' A i)
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
