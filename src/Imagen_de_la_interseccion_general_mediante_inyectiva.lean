-- Imagen_de_la_interseccion_general_mediante_inyectiva.lean
-- Imagen de la interseccion general mediante inyectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    ⋂ᵢf[Aᵢ] ⊆ f[⋂ᵢAᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ ⋂ᵢf[Aᵢ]. Entonces,
--    (∀i ∈ I)y ∈ f[Aᵢ]                                              (1)
--    y ∈ f[Aᵢ]
-- Por tanto, existe un x ∈ Aᵢ tal que
--    f(x) = y                                                       (2)
--
-- Veamos que x ∈ ⋂ᵢAᵢ. Para ello, sea j ∈ I. Por (1),
--    y ∈ f[Aⱼ]
-- Luego, existe un z tal que
--    z ∈ Aⱼ                                                         (3)
--    f(z) = y
-- Por (2),
--    f(x) = f(z)
-- y, por ser f inyectiva,
--    x = z
-- y, Por (3),
--    x ∈ Aⱼ
--
-- Puesto que x ∈ ⋂ᵢAᵢ se tiene que f(x) ∈ f[⋂ᵢAᵢ] y, por (2),
-- y ∈ f[⋂ᵢAᵢ].

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set Function

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)

-- 1ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  have h1 : ∀ (i : I), y ∈ f '' A i := mem_iInter.mp hy
  have h2 : y ∈ f '' A i := h1 i
  obtain ⟨x : α, h3 : x ∈ A i ∧ f x = y⟩ := h2
  have h4 : f x = y := h3.2
  have h5 : ∀ i : I, x ∈ A i := by
    intro j
    have h5a : y ∈ f '' A j := h1 j
    obtain ⟨z : α, h5b : z ∈ A j ∧ f z = y⟩ := h5a
    have h5c : z ∈ A j := h5b.1
    have h5d : f z = y := h5b.2
    have h5e : f z = f x := by rwa [←h4] at h5d
    have h5f : z = x := injf h5e
    show x ∈ A j
    rwa [h5f] at h5c
  have h6 : x ∈ ⋂ i, A i := mem_iInter.mpr h5
  have h7 : f x ∈ f '' (⋂ i, A i) := mem_image_of_mem f h6
  show y ∈ f '' (⋂ i, A i)
  rwa [h4] at h7

-- 2ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  rw [mem_iInter] at hy
  -- hy : ∀ (i : I), y ∈ f '' A i
  rcases hy i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ ⋂ (i : I), A i ∧ f x = y
  constructor
  . -- ⊢ x ∈ ⋂ (i : I), A i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases hy j with ⟨z, zAj, fzy⟩
    -- z : α
    -- zAj : z ∈ A j
    -- fzy : f z = y
    convert zAj
    -- ⊢ x = z
    apply injf
    -- ⊢ f x = f z
    rw [fxy]
    -- ⊢ y = f z
    rw [←fzy]
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intro y
  -- y : β
  -- ⊢ y ∈ ⋂ (i : I), f '' A i → y ∈ f '' ⋂ (i : I), A i
  simp
  -- ⊢ (∀ (i : I), ∃ x, x ∈ A i ∧ f x = y) → ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  intro h
  -- h : ∀ (i : I), ∃ x, x ∈ A i ∧ f x = y
  -- ⊢ ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  rcases h i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ (∀ (i : I), x ∈ A i) ∧ f x = y
  constructor
  . -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases h j with ⟨z, zAi, fzy⟩
    -- z : α
    -- zAi : z ∈ A j
    -- fzy : f z = y
    have : f x = f z := by rw [fxy, fzy]
    -- this : f x = f z
    have : x = z := injf this
    -- this : x = z
    rw [this]
    -- ⊢ z ∈ A j
    exact zAi
  . -- ⊢ f x = y
    exact fxy

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set α)
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
