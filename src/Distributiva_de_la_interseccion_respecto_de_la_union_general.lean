-- Distributiva_de_la_interseccion_respecto_de_la_union_general.lean
-- s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada x, se verifica que
--    x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
-- Lo demostramos mediante la siguiente cadena de equivalencias
--    x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ s ∧ x ∈ ⋃ (i : ℕ), A i
--                           ↔ x ∈ s ∧ (∃ i : ℕ, x ∈ A i)
--                           ↔ ∃ i : ℕ, x ∈ s ∧ x ∈ A i
--                           ↔ ∃ i : ℕ, x ∈ A i ∧ x ∈ s
--                           ↔ ∃ i : ℕ, x ∈ A i ∩ s
--                           ↔ x ∈ ⋃ (i : ℕ), A i ∩ s

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  calc x ∈ s ∩ ⋃ (i : ℕ), A i
     ↔ x ∈ s ∧ x ∈ ⋃ (i : ℕ), A i :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ s ∧ (∃ i : ℕ, x ∈ A i) :=
         by simp only [mem_iUnion]
   _ ↔ ∃ i : ℕ, x ∈ s ∧ x ∈ A i :=
         by simp only [exists_and_left]
   _ ↔ ∃ i : ℕ, x ∈ A i ∧ x ∈ s :=
         by simp only [and_comm]
   _ ↔ ∃ i : ℕ, x ∈ A i ∩ s :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ ⋃ (i : ℕ), A i ∩ s :=
         by simp only [mem_iUnion]

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  constructor
  . -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i → x ∈ ⋃ (i : ℕ), A i ∩ s
    intro h
    -- h : x ∈ s ∩ ⋃ (i : ℕ), A i
    -- ⊢ x ∈ ⋃ (i : ℕ), A i ∩ s
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ A i ∩ s
    rcases h with ⟨xs, xUAi⟩
    -- xs : x ∈ s
    -- xUAi : x ∈ ⋃ (i : ℕ), A i
    rw [mem_iUnion] at xUAi
    -- xUAi : ∃ i, x ∈ A i
    rcases xUAi with ⟨i, xAi⟩
    -- i : ℕ
    -- xAi : x ∈ A i
    use i
    -- ⊢ x ∈ A i ∩ s
    constructor
    . -- ⊢ x ∈ A i
      exact xAi
    . -- ⊢ x ∈ s
      exact xs
  . -- ⊢ x ∈ ⋃ (i : ℕ), A i ∩ s → x ∈ s ∩ ⋃ (i : ℕ), A i
    intro h
    -- h : x ∈ ⋃ (i : ℕ), A i ∩ s
    -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i
    rw [mem_iUnion] at h
    -- h : ∃ i, x ∈ A i ∩ s
    rcases h with ⟨i, hi⟩
    -- i : ℕ
    -- hi : x ∈ A i ∩ s
    rcases hi with ⟨xAi, xs⟩
    -- xAi : x ∈ A i
    -- xs : x ∈ s
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ ⋃ (i : ℕ), A i
      rw [mem_iUnion]
      -- ⊢ ∃ i, x ∈ A i
      use i
      -- ⊢ x ∈ A i

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  simp
  -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) ↔ (∃ i, x ∈ A i) ∧ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) → (∃ i, x ∈ A i) ∧ x ∈ s
    rintro ⟨xs, ⟨i, xAi⟩⟩
    -- xs : x ∈ s
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s
    exact ⟨⟨i, xAi⟩, xs⟩
  . -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s → x ∈ s ∧ ∃ i, x ∈ A i
    rintro ⟨⟨i, xAi⟩, xs⟩
    -- xs : x ∈ s
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ x ∈ s ∧ ∃ i, x ∈ A i
    exact ⟨xs, ⟨i, xAi⟩⟩

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  aesop

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by ext; aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- variable (a b : Prop)
-- variable (p : α → Prop)
-- #check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
-- #check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
-- #check (exists_and_left : (∃ (x : α), b ∧ p x) ↔ b ∧ ∃ (x : α), p x)
-- #check (and_comm : a ∧ b ↔ b ∧ a)
