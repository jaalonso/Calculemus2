-- Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.lean
-- Si f es inyectiva, entonces f⁻¹[f[s]] ⊆ s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    f⁻¹[f[s]] ⊆ s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x tal que
--    x ∈ f⁻¹[f[s]]
-- Entonces,
--    f(x) ∈ f[s]
-- y, por tanto, existe un
--    y ∈ s                                                          (1)
-- tal que
--    f(y) = f(x)                                                    (2)
-- De (2), puesto que f es inyectiva, se tiene que
--    y = x                                                          (3)
-- Finalmente, de (3) y (1), se tiene que
--    x ∈ s
-- que es lo que teníamos que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

open Set Function

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

-- 1ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  have h1 : f x ∈ f '' s := mem_preimage.mp hx
  have h2 : ∃ y, y ∈ s ∧ f y = f x := (mem_image f s (f x)).mp h1
  obtain ⟨y, hy : y ∈ s ∧ f y = f x⟩ := h2
  obtain ⟨ys : y ∈ s, fyx : f y = f x⟩ := hy
  have h3 : y = x := h fyx
  show x ∈ s
  exact h3 ▸ ys

-- 2ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rw [mem_image] at hx
  -- hx : ∃ x_1, x_1 ∈ s ∧ f x_1 = f x
  rcases hx with ⟨y, hy⟩
  -- y : α
  -- hy : y ∈ s ∧ f y = f x
  rcases hy with ⟨ys, fyx⟩
  -- ys : y ∈ s
  -- fyx : f y = f x
  unfold Injective at h
  -- h : ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
  have h1 : y = x := h fyx
  rw [←h1]
  -- ⊢ y ∈ s
  exact ys

-- 3ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rcases hx with ⟨y, ys, fyx⟩
  -- y : α
  -- ys : y ∈ s
  -- fyx : f y = f x
  rw [←h fyx]
  -- ⊢ y ∈ s
  exact ys

-- 4ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  rintro x ⟨y, ys, hy⟩
  -- x y : α
  -- ys : y ∈ s
  -- hy : f y = f x
  -- ⊢ x ∈ s
  rw [←h hy]
  -- ⊢ y ∈ s
  exact ys

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (y : β)
-- variable (t : Set β)
-- #check (mem_image f s y : y ∈ f '' s ↔ ∃ (x : α), x ∈ s ∧ f x = y)
-- #check (mem_preimage : x ∈ f ⁻¹' t ↔ f x ∈ t)
