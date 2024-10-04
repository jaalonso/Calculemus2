-- If_ff_is_biyective_then_f_is_biyective.lean
-- If f ∘ f is bijective, then f is bijective.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, October 4, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that if f ∘ f is bijective, then f is bijective.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- It follows from the following lemmas (proven in previous exercises):
-- + Lemma 1: If g ∘ f is injective, then f is injective.
-- + Lemma 2: If g ∘ f is surjective, then g is surjective.
-- Indeed, suppose that
--    f ∘ f is bijective
-- then it follows that
--    f ∘ f is injective                                             (1)
--    f ∘ f is surjective                                            (2)
-- From (1) and Lemma 1, it follows that
--    f is injective                                                 (3)
-- From (2) and Lemma 2, it follows that
--    f is surjective                                                (4)
-- From (3) and (4) it follows that
--    f is bijective

-- Proofs with Lean4
-- =================

import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- Proof 1
-- =======

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
by
  have h1 : Injective (f ∘ f) := Bijective.injective h
  have h2 : Surjective (f ∘ f) := Bijective.surjective h
  have h3 : Injective f := Injective.of_comp h1
  have h4 : Surjective f := Surjective.of_comp h2
  show Bijective f
  exact ⟨h3, h4⟩

-- Proof 2
-- =======

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
⟨Injective.of_comp (Bijective.injective h),
 Surjective.of_comp (Bijective.surjective h)⟩

-- Proof 3
-- =======

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
by
  constructor
  . -- ⊢ Injective f
    have h1 : Injective (f ∘ f) := Bijective.injective h
    exact Injective.of_comp h1
  . -- ⊢ Surjective f
    have h2 : Surjective (f ∘ f) := Bijective.surjective h
    exact Surjective.of_comp h2

-- Used lemmas
-- ===========

-- #check (Injective.of_comp : Injective (g ∘ f) → Injective f)
-- #check (Surjective.of_comp : Surjective (g ∘ f) → Surjective g)
