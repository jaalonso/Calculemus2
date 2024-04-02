-- Imagen_de_la_imagen_inversa.lean
-- f[f⁻¹[u]] ⊆ u.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f[f⁻¹[u]] ⊆ u
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[f⁻¹[u]]. Entonces existe un x tal que
--    x ∈ f⁻¹[u]                                                     (1)
--    f(x) = y                                                       (2)
-- Por (1),
--    f(x) ∈ u
-- y, por (2),
--    y ∈ u

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  obtain ⟨x : α, h1 : x ∈ f ⁻¹' u ∧ f x = y⟩ := h
  obtain ⟨hx : x ∈ f ⁻¹' u, fxy : f x = y⟩ := h1
  have h2 : f x ∈ u := mem_preimage.mp hx
  show y ∈ u
  exact fxy ▸ h2

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, h2⟩
  -- x : α
  -- h2 : x ∈ f ⁻¹' u ∧ f x = y
  rcases h2 with ⟨hx, fxy⟩
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, hx, fxy⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, fxy⟩
  -- y : β
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  -- ⊢ y ∈ u
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, rfl⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ f x ∈ u
  exact hx

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- Lemas usados
-- ============

-- #check (image_preimage_subset f u : f '' (f⁻¹' u) ⊆ u)
