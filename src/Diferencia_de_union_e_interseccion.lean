-- Diferencia_de_union_e_interseccion.lean
-- (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------

import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  calc x ∈ (s \ t) ∪ (t \ s)
     ↔ x ∈ (s \ t) ∨ x ∈ (t \ s) :=
         by exact mem_union x (s \ t) (t \ s)
   _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ (t \ s) :=
         by simp only [mem_diff]
   _ ↔ (x ∈ s ∨ x ∈ (t \ s)) ∧ (x ∉ t ∨ x ∈ (t \ s)) :=
         by exact and_or_right
   _ ↔ (x ∈ s ∨ (x ∈ t ∧ x ∉ s)) ∧ (x ∉ t ∨ (x ∈ t ∧ x ∉ s)) :=
         by simp only [mem_diff]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ (x ∈ s ∨ x ∉ s)) ∧
       ((x ∉ t ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp_all only [or_and_left]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ True) ∧
       (True ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp only [em (x ∈ s), em' (x ∈ t)]
   _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [and_true_iff (x ∈ s ∨ x ∈ t),
                       true_and_iff (¬x ∈ t ∨ ¬x ∈ s)]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [mem_union]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ s ∨ x ∉ t) :=
         by simp only [or_comm]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∧ x ∈ t) :=
         by simp only [not_and_or]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∩ t) :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ (s ∪ t) \ (s ∩ t)     :=
         by simp only [mem_diff]

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xs : x ∈ s
      -- xnt : ¬x ∈ t
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        left
        -- ⊢ x ∈ s
        exact xs
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨-, xt⟩
        -- xt : x ∈ t
        -- ⊢ False
        exact xnt xt
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        right
        -- ⊢ x ∈ t
        exact xt
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨xs, -⟩
        -- xs : x ∈ s
        -- ⊢ False
        exact xns xs
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      left
      -- ⊢ x ∈ s \ t
      use xs
      -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      right
      -- ⊢ x ∈ t \ s
      use xt
      -- ⊢ ¬x ∈ s
      intro xs
      -- xs : x ∈ s
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
  . rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩) <;> aesop
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩ <;> aesop

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor
  . aesop
  . aesop

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor <;> aesop

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  rw [ext_iff]
  -- ⊢ ∀ (x : α), x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  intro
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  rw [iff_def]
  -- ⊢ (x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)) ∧
  --   (x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s))
  aesop

-- 7ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by aesop (add norm ext_iff, norm iff_def)
