-- Conmutatividad_de_la_interseccion.lean
-- s ∩ t = t ∩ s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ t = t ∩ s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ s ∩ t ↔ x ∈ t ∩ s]
-- Demostratemos la equivalencia por la doble implicación.
--
-- Sea x ∈ s ∩ t. Entonces, se tiene
--    x ∈ s                                                          (1)
--    x ∈ t                                                          (2)
-- Luego x ∈ t ∩ s (por (2) y (1)).
--
-- La segunda implicación se demuestra análogamente.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
    intro h
    -- h : x ∈ s ∧ x ∈ t
    -- ⊢ x ∈ t ∧ x ∈ s
    constructor
    . -- ⊢ x ∈ t
      exact h.2
    . -- ⊢ x ∈ s
      exact h.1
  . -- ⊢ x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
    intro h
    -- h : x ∈ t ∧ x ∈ s
    -- ⊢ x ∈ s ∧ x ∈ t
    constructor
    . -- ⊢ x ∈ s
      exact h.2
    . -- ⊢ x ∈ t
      exact h.1

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  exact ⟨fun h ↦ ⟨h.2, h.1⟩,
         fun h ↦ ⟨h.2, h.1⟩⟩

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  exact ⟨fun h ↦ ⟨h.2, h.1⟩,
         fun h ↦ ⟨h.2, h.1⟩⟩

-- 4ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
    rintro ⟨xs, xt⟩
    -- xs : x ∈ s
    -- xt : x ∈ t
    -- ⊢ x ∈ t ∧ x ∈ s
    exact ⟨xt, xs⟩
  . -- ⊢ x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
    rintro ⟨xt, xs⟩
    -- xt : x ∈ t
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∧ x ∈ t
    exact ⟨xs, xt⟩

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  simp only [And.comm]

-- 6ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext (fun _ ↦ And.comm)

-- 7ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext ; simp [And.comm]

-- 8ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inter_comm s t

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Prop)
-- #check (And.comm : a ∧ b ↔ b ∧ a)
-- #check (inter_comm s t : s ∩ t = t ∩ s)
-- #check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
