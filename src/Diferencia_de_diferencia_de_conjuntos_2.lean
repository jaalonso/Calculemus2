-- Diferencia_de_diferencia_de_conjuntos_2.lean
-- s \ (t ∪ u) ⊆ (s \ t) \ u
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s \ (t ∪ u) ⊆ (s \ t) \ u
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ s \ (t ∪ u). Entonces,
--    x ∈ s                                                          (1)
--    x ∉ t ∪ u                                                      (2)
-- Tenemos que demostrar que x ∈ (s \ t) \ u; es decir, que se verifican
-- las relaciones
--    x ∈ s \ t                                                      (3)
--    x ∉ u                                                          (4)
-- Para demostrar (3) tenemos que demostrar las relaciones
--    x ∈ s                                                          (5)
--    x ∉ t                                                          (6)
-- La (5) se tiene por la (1). Para demostrar la (6), supongamos que
-- x ∈ t; entonces, x ∈ t ∪ u, en contracción con (2). Para demostrar la
-- (4), supongamos que x ∈ u; entonces, x ∈ t ∪ u, en contracción con
-- (2).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s \ (t ∪ u)
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact hx.1
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply hx.2
      -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    apply hx.2
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      exact xntu (Or.inl xt)
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    exact xntu (Or.inr xu)

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  fun _ ⟨xs, xntu⟩ ↦ ⟨⟨xs, fun xt ↦ xntu (Or.inl xt)⟩,
                      fun xu ↦ xntu (Or.inr xu)⟩

-- 4ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  aesop

-- 5ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by intro ; aesop

-- 6ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by rw [diff_diff]

-- Lema usado
-- ==========

-- #check (diff_diff : (s \ t) \ u = s \ (t ∪ u))
