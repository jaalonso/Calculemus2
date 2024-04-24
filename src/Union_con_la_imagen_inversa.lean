-- Union_con_la_imagen_inversa.lean
-- Unión con la imagen inversa
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∪ f⁻¹[v] ⊆ f⁻¹[f[s] ∪ v]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s ∪ f⁻¹[v]. Entonces, se puede dar dos casos.
--
-- Caso 1: Supongamos que x ∈ s. Entonces, se tiene
--    f(x) ∈ f[s]
--    f(x) ∈ f[s] ∪ v
--    x ∈ f⁻¹[f[s] ∪ v]
--
-- Caso 2: Supongamos que x ∈ f⁻¹[v]. Entonces, se tiene
--    f(x) ∈ v
--    f(x) ∈ f[s] ∪ v
--    x ∈ f⁻¹[f[s] ∪ v]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  cases' hx with xs xv
  . -- xs : x ∈ s
    have h1 : f x ∈ f '' s := mem_image_of_mem f xs
    have h2 : f x ∈ f '' s ∪ v := mem_union_left v h1
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h2
  . -- xv : x ∈ f ⁻¹' v
    have h3 : f x ∈ v := mem_preimage.mp xv
    have h4 : f x ∈ f '' s ∪ v := mem_union_right (f '' s) h3
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h4

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  rw [mem_preimage]
  -- ⊢ f x ∈ f '' s ∪ v
  cases' hx with xs xv
  . -- xs : x ∈ s
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- xv : x ∈ f ⁻¹' v
    apply mem_union_right
    -- ⊢ f x ∈ v
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' v
    exact xv

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  cases' hx with xs xv
  . -- xs : x ∈ s
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_right
    -- ⊢ f x ∈ v
    exact xv

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    left
    -- ⊢ f x ∈ f '' s
    exact mem_image_of_mem f xs
  . -- xv : x ∈ f ⁻¹' v
    right
    -- ⊢ f x ∈ v
    exact xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    exact Or.inl (mem_image_of_mem f xs)
  . -- xv : x ∈ f ⁻¹' v
    exact Or.inr xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x h
  -- x : α
  -- h : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  exact Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
fun _ h ↦ Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
union_preimage_subset s v f

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- variable (a b c : Prop)
-- #check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
-- #check (Or.inl : a → a ∨ b)
-- #check (Or.inr : b → a ∨ b)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
-- #check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
-- #check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
-- #check (union_preimage_subset s v f : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v))
