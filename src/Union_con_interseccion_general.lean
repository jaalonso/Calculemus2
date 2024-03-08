-- Union_con_interseccion_general.lean
-- s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para todo x,
--    x ∈ s ∪ ⋂ i, A i ↔ x ∈ ⋂ i, A i ∪ s
-- Lo haremos mediante la siguiente cadena de equivalencias
--    x ∈ s ∪ ⋂ i, A i ↔ x ∈ s ∨ x ∈ ⋂ i, A i
--                     ↔ x ∈ s ∨ ∀ i, x ∈ A i
--                     ↔ ∀ i, x ∈ s ∨ x ∈ A i
--                     ↔ ∀ i, x ∈ A i ∨ x ∈ s
--                     ↔ ∀ i, x ∈ A i ∪ s
--                     ↔ x ∈ ⋂ i, A i ∪ s

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

-- 1ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  calc x ∈ s ∪ ⋂ i, A i
     ↔ x ∈ s ∨ x ∈ ⋂ i, A i :=
         by simp only [mem_union]
   _ ↔ x ∈ s ∨ ∀ i, x ∈ A i :=
         by simp only [mem_iInter]
   _ ↔ ∀ i, x ∈ s ∨ x ∈ A i :=
         by simp only [forall_or_left]
   _ ↔ ∀ i, x ∈ A i ∨ x ∈ s  :=
         by simp only [or_comm]
   _ ↔ ∀ i, x ∈ A i ∪ s  :=
         by simp only [mem_union]
   _ ↔ x ∈ ⋂ i, A i ∪ s :=
         by simp only [mem_iInter]

-- 2ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  simp only [mem_union, mem_iInter]
  -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) ↔ ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) → ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    intros h i
    -- h : x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    -- i : ℕ
    -- ⊢ x ∈ A i ∨ x ∈ s
    rcases h with (xs | xAi)
    . -- xs : x ∈ s
      right
      -- ⊢ x ∈ s
      exact xs
    . -- xAi : ∀ (i : ℕ), x ∈ A i
      left
      -- ⊢ x ∈ A i
      exact xAi i
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∨ x ∈ s) → x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    -- ⊢ x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    by_cases cxs : x ∈ s
    . -- cxs : x ∈ s
      left
      -- ⊢ x ∈ s
      exact cxs
    . -- cns : ¬x ∈ s
      right
      -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      rcases h i with (xAi | xs)
      . -- ⊢ x ∈ A i
        exact xAi
      . -- xs : x ∈ s
        exact absurd xs cxs

-- 3ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  simp only [mem_union, mem_iInter]
  -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) ↔ ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) → ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    rintro (xs | xI) i
    . -- xs : x ∈ s
      -- i : ℕ
      -- ⊢ x ∈ A i ∨ x ∈ s
      right
      -- ⊢ x ∈ s
      exact xs
    . -- xI : ∀ (i : ℕ), x ∈ A i
      -- i : ℕ
      -- ⊢ x ∈ A i ∨ x ∈ s
      left
      -- ⊢ x ∈ A i
      exact xI i
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∨ x ∈ s) → x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    -- ⊢ x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    by_cases cxs : x ∈ s
    . -- cxs : x ∈ s
      left
      -- ⊢ x ∈ s
      exact cxs
    . -- cxs : ¬x ∈ s
      right
      -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      cases h i
      . -- h : x ∈ A i
        assumption
      . -- h : x ∈ s
        contradiction

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s t : Set α)
-- variable (a b q : Prop)
-- variable (p : ℕ → Prop)
-- #check (absurd : a → ¬a → b)
-- #check (forall_or_left : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x)
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_union x a b : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
-- #check (or_comm : a ∨ b ↔ b ∨ a)
