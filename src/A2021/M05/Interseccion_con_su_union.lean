-- Interseccion_con_su_union.lean
-- s ∩ (s ∪ t) = s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

-- Demostación en lenguaje natural
-- ===============================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ s ∩ (s ∪ t) ↔ x ∈ s]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Sea x ∈ s ∩ (s ∪ t). Entonces, x ∈ s.
--
-- (⟸) Sea x ∈ s. Entonces, x ∈ s ∪ t y, por tanto,
-- x ∈ s ∩ (s ∪ t).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intros h
  -- h : x ∈ s ∩ (s ∪ t)
  -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intro h
    -- h : x ∈ s ∩ (s ∪ t)
    -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      exact (Or.inl xs)

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨fun h ↦ h.1,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨And.left,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    rintro ⟨xs, -⟩
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    use xs
    -- ⊢ x ∈ s ∪ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  apply subset_antisymm
  . -- ⊢ s ∩ (s ∪ t) ⊆ s
    rintro x ⟨hxs, -⟩
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ s ⊆ s ∩ (s ∪ t)
    intros x hxs
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    exact ⟨hxs, Or.inl hxs⟩

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self

-- 8ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by aesop

-- Lemas usados
-- ============

-- variable (a b : Prop)
-- #check (And.left : a ∧ b → a)
-- #check (Or.inl : a → a ∨ b)
-- #check (inf_sup_self : s ∩ (s ∪ t) = s)
-- #check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)
