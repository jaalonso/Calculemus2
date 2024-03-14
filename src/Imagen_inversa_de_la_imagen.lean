-- Imagen_inversa_de_la_imagen.lean
-- s ⊆ f⁻¹[f[s]]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si s es un subconjunto del dominio de la función f,
-- entonces s está contenido en la imagen inversa de la imagen de s por
-- f; es decir,
--    s ⊆ f⁻¹[f[s]]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra mediante la siguiente cadena de implicaciones
--    x ∈ s ⟹ f(x) ∈ f[s]
--          ⟹ x ∈ f⁻¹[f[s]]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

-- 1ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  have h1 : f x ∈ f '' s := mem_image_of_mem f xs
  show x ∈ f ⁻¹' (f '' s)
  exact mem_preimage.mp h1

-- 2ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  apply mem_preimage.mpr
  -- ⊢ f x ∈ f '' s
  apply mem_image_of_mem
  -- ⊢ x ∈ s
  exact xs

-- 3ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  apply mem_image_of_mem
  -- ⊢ x ∈ s
  exact xs

-- 4ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
fun _ ↦ mem_image_of_mem f

-- 5ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  show f x ∈ f '' s
  use x, xs

-- 6ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  use x, xs

-- 7ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
subset_preimage_image f s

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set β)
-- #check (mem_preimage : x ∈ f ⁻¹' t ↔ f x ∈ t)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (subset_preimage_image f s : s ⊆ f ⁻¹' (f '' s))
