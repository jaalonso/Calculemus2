-- Union_con_la_imagen.lean
-- Unión con la imagen
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ f[s ∪ f⁻¹[v]]. Entonces, existe un x tal que
--    x ∈ s ∪ f⁻¹[v]                                                 (1)
--    f(x) = y                                                       (2)
-- De (1), se tiene que x ∈ s ó x ∈ f⁻¹[v]. Vamos a demostrar en ambos
-- casos que
--    y ∈ f[s] ∪ v
--
-- Caso 1: Supongamos que x ∈ s. Entonces,
--    f(x) ∈ f[s]
-- y, por (2), se tiene que
--    y ∈ f[s]
-- Por tanto,
--    y ∈ f[s] ∪ v
--
-- Caso 2: Supongamos que x ∈ f⁻¹[v]. Entonces,
--    f(x) ∈ v
-- y, por (2), se tiene que
--    y ∈ v
-- Por tanto,
--    y ∈ f[s] ∪ v

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable (α β : Type _)
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  intros y hy
  obtain ⟨x : α, hx : x ∈ s ∪ f ⁻¹' v ∧ f x = y⟩ := hy
  obtain ⟨hx1 : x ∈ s ∪ f ⁻¹' v, fxy : f x = y⟩ := hx
  cases' hx1 with xs xv
  . -- xs : x ∈ s
    have h1 : f x ∈ f '' s := mem_image_of_mem f xs
    have h2 : y ∈ f '' s := by rwa [fxy] at h1
    show y ∈ f '' s ∪ v
    exact mem_union_left v h2
  . -- xv : x ∈ f ⁻¹' v
    have h3 : f x ∈ v := mem_preimage.mp xv
    have h4 : y ∈ v := by rwa [fxy] at h3
    show y ∈ f '' s ∪ v
    exact mem_union_right (f '' s) h4

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  intros y hy
  obtain ⟨x : α, hx : x ∈ s ∪ f ⁻¹' v ∧ f x = y⟩ := hy
  obtain ⟨hx1 : x ∈ s ∪ f ⁻¹' v, fxy : f x = y⟩ := hx
  cases' hx1 with xs xv
  . -- xs : x ∈ s
    left
    -- ⊢ y ∈ f '' s
    use x
  . -- ⊢ y ∈ f '' s ∪ v
    right
    -- ⊢ y ∈ v
    rw [←fxy]
    -- ⊢ f x ∈ v
    exact xv

-- 2ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  rintro y ⟨x, xs | xv, fxy⟩
  -- y : β
  -- x : α
  . -- xs : x ∈ s
    -- ⊢ y ∈ f '' s ∪ v
    left
    -- ⊢ y ∈ f '' s
    use x, xs
  . -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∪ v
    right
    -- ⊢ y ∈ v
    rw [←fxy]
    -- ⊢ f x ∈ v
    exact xv

-- 3ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  rintro y ⟨x, xs | xv, fxy⟩ <;>
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
-- #check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
-- #check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
