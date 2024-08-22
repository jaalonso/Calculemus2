-- Imagen_de_la_union_general.lean
-- Imagen de la unión general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-abril-2024
-- ---------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Demostrar que
--    f[⋃ᵢAᵢ] = ⋃ᵢf[Aᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo y,
--    y ∈ f[⋃ᵢAᵢ] ↔ y ∈ ⋃ᵢf[Aᵢ]
-- Lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que y ∈ f[⋃ᵢAᵢ]. Entonces, existe un x tal que
--    x ∈ ⋃ᵢAᵢ                                                       (1)
--    f(x) = y                                                       (2)
-- Por (1), existe un i tal que
--    i ∈ ℕ                                                          (3)
--    x ∈ Aᵢ                                                         (4)
-- Por (4),
--    f(x) ∈ f[Aᵢ]
-- Por (3),
--    f(x) ∈ ⋃ᵢf[Aᵢ]
-- y, por (2),
--    y ∈ ⋃ᵢf[Aᵢ]
--
-- (⟸) Supongamos que y ∈ ⋃ᵢf[Aᵢ]. Entonces, existe un i tal que
--    i ∈ ℕ                                                          (5)
--    y ∈ f[Aᵢ]                                                      (6)
-- Por (6), existe un x tal que
--    x ∈ Aᵢ                                                         (7)
--    f(x) = y                                                       (8)
-- Por (5) y (7),
--    x ∈ ⋃ᵢAᵢ
-- Luego,
--    f(x) ∈ f[⋃ᵢAᵢ]
-- y, por (8),
--    y ∈ f[⋃ᵢAᵢ]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (A : ℕ → Set α)

-- 1ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  constructor
  . -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i → y ∈ ⋃ (i : ℕ), f '' A i
    intro hy
    -- hy : y ∈ f '' ⋃ (i : ℕ), A i
    -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i
    have h1 : ∃ x, x ∈ ⋃ i, A i ∧ f x = y := (mem_image f (⋃ i, A i) y).mp hy
    obtain ⟨x, hx : x ∈ ⋃ i, A i ∧ f x = y⟩ := h1
    have xUA : x ∈ ⋃ i, A i := hx.1
    have fxy : f x = y := hx.2
    have xUA : ∃ i, x ∈ A i := mem_iUnion.mp xUA
    obtain ⟨i, xAi : x ∈ A i⟩ := xUA
    have h2 : f x ∈ f '' A i := mem_image_of_mem f xAi
    have h3 : f x ∈ ⋃ i, f '' A i := mem_iUnion_of_mem i h2
    show y ∈ ⋃ i, f '' A i
    rwa [fxy] at h3
  . -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i → y ∈ f '' ⋃ (i : ℕ), A i
    intro hy
    -- hy : y ∈ ⋃ (i : ℕ), f '' A i
    -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i
    have h4 : ∃ i, y ∈ f '' A i := mem_iUnion.mp hy
    obtain ⟨i, h5 : y ∈ f '' A i⟩ := h4
    have h6 : ∃ x, x ∈ A i ∧ f x = y := (mem_image f (A i) y).mp h5
    obtain ⟨x, h7 : x ∈ A i ∧ f x = y⟩ := h6
    have h8 : x ∈ A i := h7.1
    have h9 : x ∈ ⋃ i, A i := mem_iUnion_of_mem i h8
    have h10 : f x ∈ f '' (⋃ i, A i) := mem_image_of_mem f h9
    show y ∈ f '' (⋃ i, A i)
    rwa [h7.2] at h10

-- 2ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  constructor
  . -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i → y ∈ ⋃ (i : ℕ), f '' A i
    intro hy
    -- hy : y ∈ f '' ⋃ (i : ℕ), A i
    -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i
    rw [mem_image] at hy
    -- hy : ∃ x, x ∈ ⋃ (i : ℕ), A i ∧ f x = y
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ ⋃ (i : ℕ), A i ∧ f x = y
    cases' hx with xUA fxy
    -- xUA : x ∈ ⋃ (i : ℕ), A i
    -- fxy : f x = y
    rw [mem_iUnion] at xUA
    -- xUA : ∃ i, x ∈ A i
    cases' xUA with i xAi
    -- i : ℕ
    -- xAi : x ∈ A i
    rw [mem_iUnion]
    -- ⊢ ∃ i, y ∈ f '' A i
    use i
    -- ⊢ y ∈ f '' A i
    rw [←fxy]
    -- ⊢ f x ∈ f '' A i
    apply mem_image_of_mem
    -- ⊢ x ∈ A i
    exact xAi
  . -- ⊢ y ∈ ⋃ (i : ℕ), f '' A i → y ∈ f '' ⋃ (i : ℕ), A i
    intro hy
    -- hy : y ∈ ⋃ (i : ℕ), f '' A i
    -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i
    rw [mem_iUnion] at hy
    -- hy : ∃ i, y ∈ f '' A i
    cases' hy with i yAi
    -- i : ℕ
    -- yAi : y ∈ f '' A i
    cases' yAi with x hx
    -- x : α
    -- hx : x ∈ A i ∧ f x = y
    cases' hx with xAi fxy
    -- xAi : x ∈ A i
    -- fxy : f x = y
    rw [←fxy]
    -- ⊢ f x ∈ f '' ⋃ (i : ℕ), A i
    apply mem_image_of_mem
    -- ⊢ x ∈ ⋃ (i : ℕ), A i
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ A i
    use i

-- 3ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' ⋃ (i : ℕ), A i ↔ y ∈ ⋃ (i : ℕ), f '' A i
  simp
  -- ⊢ (∃ x, (∃ i, x ∈ A i) ∧ f x = y) ↔ ∃ i x, x ∈ A i ∧ f x = y
  constructor
  . -- ⊢ (∃ x, (∃ i, x ∈ A i) ∧ f x = y) → ∃ i x, x ∈ A i ∧ f x = y
    rintro ⟨x, ⟨i, xAi⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ ∃ i x, x ∈ A i ∧ f x = y
    use i, x, xAi
  . -- ⊢ (∃ i x, x ∈ A i ∧ f x = y) → ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    rintro ⟨i, x, xAi, fxy⟩
    -- i : ℕ
    -- x : α
    -- xAi : x ∈ A i
    -- fxy : f x = y
    -- ⊢ ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    exact ⟨x, ⟨i, xAi⟩, fxy⟩

-- 4ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
image_iUnion

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (y : β)
-- variable (s : Set α)
-- variable (i : ℕ)
-- #check (image_iUnion : f '' ⋃ i, A i = ⋃ i, f '' A i)
-- #check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
-- #check (mem_iUnion_of_mem i : x ∈ A i → x ∈ ⋃ i, A i)
-- #check (mem_image f s y : (y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y))
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
