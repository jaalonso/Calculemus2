-- Interseccion_de_intersecciones.lean
-- (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para x se verifica
--    x ∈ ⋂ i, (A i ∩ B i) ↔ x ∈ (⋂ i, A i) ∩ (⋂ i, B i)
-- Lo demostramos mediante la siguiente cadena de equivalencias
--    x ∈ ⋂ i, (A i ∩ B i) ↔ (∀ i)[x ∈ A i ∩ B i]
--                         ↔ (∀ i)[x ∈ A i ∧ x ∈ B i]
--                         ↔ (∀ i)[x ∈ A i] ∧ (∀ i)[x ∈ B i]
--                         ↔ x ∈ (⋂ i, A i) ∧ x ∈ (⋂ i, B i)
--                         ↔ x ∈ (⋂ i, A i) ∩ (⋂ i, B i)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (A B : ℕ → Set α)

-- 1ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  calc x ∈ ⋂ i, A i ∩ B i
     ↔ ∀ i, x ∈ A i ∩ B i :=
         by exact mem_iInter
   _ ↔ ∀ i, x ∈ A i ∧ x ∈ B i :=
         by simp only [mem_inter_iff]
   _ ↔ (∀ i, x ∈ A i) ∧ (∀ i, x ∈ B i) :=
         by exact forall_and
   _ ↔ x ∈ (⋂ i, A i) ∧ x ∈ (⋂ i, B i) :=
         by simp only [mem_iInter]
   _ ↔ x ∈ (⋂ i, A i) ∩ ⋂ i, B i :=
         by simp only [mem_inter_iff]

-- 2ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  constructor
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) → (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    -- ⊢ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      exact (h i).1
    . -- ⊢ ∀ (i : ℕ), x ∈ B i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ B i
      exact (h i).2
  . -- ⊢ ((∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i) → ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    intros h i
    -- h : (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    -- i : ℕ
    -- ⊢ x ∈ A i ∧ x ∈ B i
    rcases h with ⟨h1, h2⟩
    -- h1 : ∀ (i : ℕ), x ∈ A i
    -- h2 : ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ x ∈ A i
      exact h1 i
    . -- ⊢ x ∈ B i
      exact h2 i

-- 3ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  exact ⟨fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩,
         fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2 i⟩⟩

-- 4ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Set α)
-- variable (ι : Sort v)
-- variable (s : ι → Set α)
-- variable (p q : α → Prop)
-- #check (forall_and : (∀ (x : α), p x ∧ q x) ↔ (∀ (x : α), p x) ∧ ∀ (x : α), q x)
-- #check (mem_iInter : x ∈ ⋂ (i : ι), s i ↔ ∀ (i : ι), x ∈ s i)
-- #check (mem_inter_iff x a b : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b)
