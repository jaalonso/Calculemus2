-- Subconjunto_de_la_imagen_inversa.lean
-- f[s] ⊆ u ↔ s ⊆ f⁻¹[u]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f[s] ⊆ u ↔ s ⊆ f⁻¹[u]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Los demostraremos probando las dos implicaciones.
--
-- (⟹) Supongamos que
--    f[s] ⊆ u                                                       (1)
-- y tenemos que demostrar que
--    s ⊆ f⁻¹[u]
-- Se prueba mediante las siguientes implicaciones
--    x ∈ s ⟹ f(x) ∈ f[s]
--          ⟹ f(x) ∈ u       [por (1)]
--          ⟹ x ∈ f⁻¹[u]
--
-- (⟸) Supongamos que
--    s ⊆ f⁻¹[u]                                                     (2)
-- y tenemos que demostrar que
--    f[s] ⊆ u
-- Para ello, sea y ∈ f[s]. Entonces, existe un
--    x ∈ s                                                          (3)
-- tal que
--    y = f(x)                                                       (4)
-- Entonces,
--    x ∈ f⁻¹[u]    [por (2) y (3)]
--    ⟹ f(x) ∈ u
--    ⟹ y ∈ u     [por (4)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (u : Set β)

-- 1ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
calc f '' s ⊆ u
   ↔ ∀ y, y ∈ f '' s → y ∈ u :=
       by simp only [subset_def]
 _ ↔ ∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u :=
       by simp only [mem_image]
 _ ↔ ∀ x, x ∈ s → f x ∈ u := by
       constructor
       . -- (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u) → (∀ x, x ∈ s → f x ∈ u)
         intro h x xs
         -- h : ∀ (y : β), (∃ x, x ∈ s ∧ f x = y) → y ∈ u
         -- x : α
         -- xs : x ∈ s
         -- ⊢ f x ∈ u
         exact h (f x) (by use x, xs)
       . -- (∀ x, x ∈ s → f x ∈ u) → (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u)
         intro h y hy
         -- h : ∀ (x : α), x ∈ s → f x ∈ u
         -- y : β
         -- hy : ∃ x, x ∈ s ∧ f x = y
         -- ⊢ y ∈ u
         obtain ⟨x, hx⟩ := hy
         -- x : α
         -- hx : x ∈ s ∧ f x = y
         have h1 : y = f x := hx.2.symm
         have h2 : f x ∈ u := h x hx.1
         show y ∈ u
         exact mem_of_eq_of_mem h1 h2
 _ ↔ ∀ x, x ∈ s → x ∈ f ⁻¹' u :=
       by simp only [mem_preimage]
 _ ↔ s ⊆ f ⁻¹' u :=
       by simp only [subset_def]

-- 2ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
calc f '' s ⊆ u
   ↔ ∀ y, y ∈ f '' s → y ∈ u :=
       by simp only [subset_def]
 _ ↔ ∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u :=
       by simp only [mem_image]
 _ ↔ ∀ x, x ∈ s → f x ∈ u := by
       constructor
       . -- (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u) → (∀ x, x ∈ s → f x ∈ u)
         intro h x xs
         -- h : ∀ (y : β), (∃ x, x ∈ s ∧ f x = y) → y ∈ u
         -- x : α
         -- xs : x ∈ s
         -- ⊢ f x ∈ u
         apply h (f x)
         -- ⊢ ∃ x_1, x_1 ∈ s ∧ f x_1 = f x
         use x, xs
       . -- (∀ x, x ∈ s → f x ∈ u) → (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u)
         intro h y hy
         -- h : ∀ (x : α), x ∈ s → f x ∈ u
         -- y : β
         -- hy : ∃ x, x ∈ s ∧ f x = y
         -- ⊢ y ∈ u
         obtain ⟨x, hx⟩ := hy
         -- x : α
         -- hx : x ∈ s ∧ f x = y
         rw [←hx.2]
         -- ⊢ f x ∈ u
         apply h x
         -- ⊢ x ∈ s
         exact hx.1
 _ ↔ ∀ x, x ∈ s → x ∈ f ⁻¹' u :=
       by simp only [mem_preimage]
 _ ↔ s ⊆ f ⁻¹' u :=
       by simp only [subset_def]

-- 3ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by
  constructor
  . -- ⊢ f '' s ⊆ u → s ⊆ f ⁻¹' u
    intros h x xs
    -- h : f '' s ⊆ u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ x ∈ f ⁻¹' u
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u
    apply h
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ s ⊆ f ⁻¹' u → f '' s ⊆ u
    intros h y hy
    -- h : s ⊆ f ⁻¹' u
    -- y : β
    -- hy : y ∈ f '' s
    -- ⊢ y ∈ u
    rcases hy with ⟨x, xs, fxy⟩
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    rw [←fxy]
    -- ⊢ f x ∈ u
    exact h xs

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by
  constructor
  . -- ⊢ f '' s ⊆ u → s ⊆ f ⁻¹' u
    intros h x xs
    -- h : f '' s ⊆ u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ x ∈ f ⁻¹' u
    apply h
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ s ⊆ f ⁻¹' u → f '' s ⊆ u
    rintro h y ⟨x, xs, rfl⟩
    -- h : s ⊆ f ⁻¹' u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ f x ∈ u
    exact h xs

-- 5ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
image_subset_iff

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by simp

-- Lemas usados
-- ============

-- variable (x y : α)
-- #check (image_subset_iff : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (mem_of_eq_of_mem : x = y → y ∈ s → x ∈ s)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
