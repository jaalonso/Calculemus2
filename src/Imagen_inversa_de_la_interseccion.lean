-- Imagen_inversa_de_la_interseccion.lean
-- f⁻¹[u ∩ v] = f⁻¹[u] ∩ f⁻¹[v]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, la imagen inversa de un conjunto s (de elementos de tipo β)
-- por la función f (de tipo α → β) es el conjunto `f ⁻¹' s` de
-- elementos x (de tipo α) tales que `f x ∈ s`.
--
-- Demostrar que
--    f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ f⁻¹[u ∩ v] ↔ x ∈ f⁻¹[u] ∩ f⁻¹[v]
-- Lo haremos mediante la siguiente cadena de equivalencias
--    x ∈ f⁻¹[u ∩ v] ↔ f x ∈ u ∩ v
--                   ↔ f x ∈ u ∧ f x ∈ v
--                   ↔ x ∈ f⁻¹[u] ∧ x ∈ f⁻¹[v]
--                   ↔ x ∈ f⁻¹[u] ∩ f⁻¹[v]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)

open Set

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  calc x ∈ f ⁻¹' (u ∩ v)
     ↔ f x ∈ u ∩ v :=
         by simp only [mem_preimage]
   _ ↔ f x ∈ u ∧ f x ∈ v :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ f ⁻¹' u ∧ x ∈ f ⁻¹' v :=
         by simp only [mem_preimage]
   _ ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v :=
         by simp only [mem_inter_iff]

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∩ v) → x ∈ f ⁻¹' u ∩ f ⁻¹' v
    intro h
    -- h : x ∈ f ⁻¹' (u ∩ v)
    -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v
    constructor
    . -- ⊢ x ∈ f ⁻¹' u
      apply mem_preimage.mpr
      -- ⊢ f x ∈ u
      rw [mem_preimage] at h
      -- h : f x ∈ u ∩ v
      exact mem_of_mem_inter_left h
    . -- ⊢ x ∈ f ⁻¹' v
      apply mem_preimage.mpr
      -- ⊢ f x ∈ v
      rw [mem_preimage] at h
      -- h : f x ∈ u ∩ v
      exact mem_of_mem_inter_right h
  . -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v → x ∈ f ⁻¹' (u ∩ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∩ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∩ v)
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u ∩ v
    constructor
    . -- ⊢ f x ∈ u
      apply mem_preimage.mp
      -- ⊢ x ∈ f ⁻¹' u
      exact mem_of_mem_inter_left h
    . -- ⊢ f x ∈ v
      apply mem_preimage.mp
      -- ⊢ x ∈ f ⁻¹' v
      exact mem_of_mem_inter_right h

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∩ v) → x ∈ f ⁻¹' u ∩ f ⁻¹' v
    intro h
    -- h : x ∈ f ⁻¹' (u ∩ v)
    -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v
    constructor
    . -- ⊢ x ∈ f ⁻¹' u
      simp at *
      -- h : f x ∈ u ∧ f x ∈ v
      -- ⊢ f x ∈ u
      exact h.1
    . -- ⊢ x ∈ f ⁻¹' v
      simp at *
      -- h : f x ∈ u ∧ f x ∈ v
      -- ⊢ f x ∈ v
      exact h.2
  . -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v → x ∈ f ⁻¹' (u ∩ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∩ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∩ v)
    simp at *
    -- h : f x ∈ u ∧ f x ∈ v
    -- ⊢ f x ∈ u ∧ f x ∈ v
    exact h

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by aesop

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
preimage_inter

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
rfl

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s t : Set α)
-- #check (mem_of_mem_inter_left : x ∈ s ∩ t → x ∈ s)
-- #check (mem_of_mem_inter_right : x ∈ s ∩ t → x ∈ t)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
-- #check (preimage_inter : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v)
