-- Union_con_su_diferencia.lean
-- (s \ t) ∪ t = s ∪ t.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1 de marzo de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s \ t) ∪ t = s ∪ t
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t]
-- y lo demostraremos por la siguiente cadena de equivalencias:
--    x ∈ (s \ t) ∪ t ↔ x ∈ (s \ t) ∨ (x ∈ t)
--                    ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t
--                    ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t)
--                    ↔ x ∈ s ∨ x ∈ t
--                    ↔ x ∈ s ∪ t

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  calc x ∈ (s \ t) ∪ t
       ↔ x ∈ s \ t ∨ x ∈ t                 := mem_union x (s \ t) t
     _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t           := by simp only [mem_diff x]
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t) := and_or_right
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ True            := by simp only [em' (x ∈ t)]
     _ ↔ x ∈ s ∨ x ∈ t                     := and_true_iff (x ∈ s ∨ x ∈ t)
     _ ↔ x ∈ s ∪ t                         := (mem_union x s t).symm

-- 2ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    intro hx
    -- hx : x ∈ (s \ t) ∪ t
    -- ⊢ x ∈ s ∪ t
    rcases hx with (xst | xt)
    . -- xst : x ∈ s \ t
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xst.1
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      intro hx
      -- hx : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      rcases hx with (xs | xt)
      . -- xs : x ∈ s
        left
        -- ⊢ x ∈ s \ t
        constructor
        . -- ⊢ x ∈ s
          exact xs
        . -- ⊢ ¬x ∈ t
          exact h
      . -- xt : x ∈ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 3ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    rintro (⟨xs, -⟩ | xt)
    . -- xs : x ∈ s
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      rintro (xs | xt)
      . -- xs : x ∈ s
        -- ⊢ x ∈ (s \ t) ∪ t
        left
        -- ⊢ x ∈ s \ t
        exact ⟨xs, h⟩
      . -- xt : x ∈ t
        -- ⊢ x ∈ (s \ t) ∪ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 4ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
diff_union_self

-- 5ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s \ t ∪ t ↔ x ∈ s ∪ t
  simp

-- 6ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by simp

-- Lemas usados
-- ============

-- variable (a b c : Prop)
-- variable (x : α)
-- #check (and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c))
-- #check (and_true_iff a : a ∧ True ↔ a)
-- #check (diff_union_self : (s \ t) ∪ t = s ∪ t)
-- #check (em' a : ¬a ∨ a)
-- #check (mem_diff x : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t)
-- #check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
