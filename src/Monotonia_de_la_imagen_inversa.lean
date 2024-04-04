-- Monotonia_de_la_imagen_inversa.lean
-- Si u ⊆ v, entonces f⁻¹[u] ⊆ f⁻¹[v].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si u ⊆ v, entonces
--    f ⁻¹' u ⊆ f ⁻¹' v
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de implicaciones:
--    x ∈ f⁻¹[u] ⟹ f(x) ∈ u
--               ⟹ f(x) ∈ v      [porque u ⊆ v]
--               ⟹ x ∈ f⁻¹[v]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)

-- 1ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  have h1 : f x ∈ u := mem_preimage.mp hx
  have h2 : f x ∈ v := h h1
  show x ∈ f ⁻¹' v
  exact mem_preimage.mpr h2

-- 2ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply mem_preimage.mpr
  -- ⊢ f x ∈ v
  apply h
  -- ⊢ f x ∈ u
  apply mem_preimage.mp
  -- ⊢ x ∈ f ⁻¹' u
  exact hx

-- 3ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply h
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  exact h hx

-- 5ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
fun _ hx ↦ h hx

-- 6ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- 7ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
preimage_mono h

-- 8ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by tauto

-- Lemas usados
-- ============

-- variable (a : α)
-- #check (mem_preimage : a ∈ f ⁻¹' u ↔ f a ∈ u)
-- #check (preimage_mono : u ⊆ v → f ⁻¹' u ⊆ f ⁻¹' v)
