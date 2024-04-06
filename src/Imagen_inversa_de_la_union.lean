-- Imagen_inversa_de_la_union.lean
-- f⁻¹[A ∪ B] = f⁻¹[A] ∪ f⁻¹[B].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ f⁻¹[A ∪ B] ↔ x ∈ f⁻¹[A] ∪ f⁻¹[B]
-- Lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que x ∈ f⁻¹[A ∪ B]. Entonces, f(x) ∈ A ∪ B.
-- Distinguimos dos casos:
--
-- Caso 1: Supongamos que f(x) ∈ A. Entonces, x ∈ f⁻¹[A] y, por tanto,
-- x ∈ f⁻¹[A] ∪ f⁻¹[B].
--
-- Caso 2: Supongamos que f(x) ∈ B. Entonces, x ∈ f⁻¹[B] y, por tanto,
-- x ∈ f⁻¹[A] ∪ f⁻¹[B].
--
-- (⟸) Supongamos que x ∈ f⁻¹[A] ∪ f⁻¹[B]. Distinguimos dos casos.
--
-- Caso 1: Supongamos que x ∈ f⁻¹[A]. Entonces, f(x) ∈ A y, por tanto,
-- f(x) ∈ A ∪ B. Luego, x ∈ f⁻¹[A ∪ B].
--
-- Caso 2: Supongamos que x ∈ f⁻¹[B]. Entonces, f(x) ∈ B y, por tanto,
-- f(x) ∈ A ∪ B. Luego, x ∈ f⁻¹[A ∪ B].

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (A B : Set β)

-- 1ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    intro h
    -- h : x ∈ f ⁻¹' (A ∪ B)
    -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rw [mem_preimage] at h
    -- h : f x ∈ A ∪ B
    rcases h with fxA | fxB
    . -- fxA : f x ∈ A
      left
      -- ⊢ x ∈ f ⁻¹' A
      apply mem_preimage.mpr
      -- ⊢ f x ∈ A
      exact fxA
    . -- fxB : f x ∈ B
      right
      -- ⊢ x ∈ f ⁻¹' B
      apply mem_preimage.mpr
      -- ⊢ f x ∈ B
      exact fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    intro h
    -- h : x ∈ f ⁻¹' A ∪ f ⁻¹' B
    -- ⊢ x ∈ f ⁻¹' (A ∪ B)
    rw [mem_preimage]
    -- ⊢ f x ∈ A ∪ B
    rcases h with xfA | xfB
    . -- xfA : x ∈ f ⁻¹' A
      rw [mem_preimage] at xfA
      -- xfA : f x ∈ A
      left
      -- ⊢ f x ∈ A
      exact xfA
    . -- xfB : x ∈ f ⁻¹' B
      rw [mem_preimage] at xfB
      -- xfB : f x ∈ B
      right
      -- ⊢ f x ∈ B
      exact xfB

-- 2ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    intros h
    -- h : x ∈ f ⁻¹' (A ∪ B)
    -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rcases h with fxA | fxB
    . -- fxA : f x ∈ A
      left
      -- ⊢ x ∈ f ⁻¹' A
      exact fxA
    . -- fxB : f x ∈ B
      right
      -- ⊢ x ∈ f ⁻¹' B
      exact fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    intro h
    -- h : x ∈ f ⁻¹' A ∪ f ⁻¹' B
    -- ⊢ x ∈ f ⁻¹' (A ∪ B)
    rcases h with xfA | xfB
    . -- xfA : x ∈ f ⁻¹' A
      left
      -- ⊢ f x ∈ A
      exact xfA
    . -- xfB : x ∈ f ⁻¹' B
      right
      -- ⊢ f x ∈ B
      exact xfB

-- 3ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rintro (fxA | fxB)
    . -- fxA : f x ∈ A
      -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
      exact Or.inl fxA
    . -- fxB : f x ∈ B
      -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
      exact Or.inr fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    rintro (xfA | xfB)
    . -- xfA : x ∈ f ⁻¹' A
      -- ⊢ x ∈ f ⁻¹' (A ∪ B)
      exact Or.inl xfA
    . -- xfB : x ∈ f ⁻¹' B
      -- ⊢ x ∈ f ⁻¹' (A ∪ B)
      exact Or.inr xfB

-- 4ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    aesop
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    aesop

-- 5ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  aesop

-- 6ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by ext ; aesop

-- 7ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by ext ; rfl

-- 8ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
rfl

-- 9ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
preimage_union

-- 10ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by simp

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (p q : Prop)
-- #check (Or.inl: p → p ∨ q)
-- #check (Or.inr: q → p ∨ q)
-- #check (mem_preimage : x ∈ f ⁻¹' A ↔ f x ∈ A)
-- #check (preimage_union : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B)
