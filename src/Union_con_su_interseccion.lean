-- Union_con_su_interseccion.lean
-- s ∪ (s ∩ t) = s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29 de febrero de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x)[x ∈ s ∪ (s ∩ t) ↔ x ∈ s]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Sea x ∈ s ∪ (s ∩ t). Entonces, c ∈ s o x ∈ s ∩ t. En ambos casos,
-- x ∈ s.
--
-- (⟸) Sea x ∈ s. Entonces, x ∈ s ∩ t y, por tanto, x ∈ s ∪ (s ∩ t).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    intro hx
    -- hx : x ∈ s ∪ (s ∩ t)
    -- ⊢ x ∈ s
    rcases hx with (xs | xst)
    . -- xs : x ∈ s
      exact xs
    . -- xst : x ∈ s ∩ t
      exact xst.1
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ (s ∩ t)
    left
    -- ⊢ x ∈ s
    exact xs

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ s ∩ t ↔ x ∈ s
  exact ⟨fun hx ↦ Or.elim hx id And.left,
         fun xs ↦ Or.inl xs⟩

-- 3ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    rintro (xs | ⟨xs, -⟩) <;>
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ s ∩ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self

-- Lemas usados
-- ============

-- variable (a b c : Prop)
-- #check (And.left : a ∧ b → a)
-- #check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
-- #check (sup_inf_self : s ∪ (s ∩ t) = s)
