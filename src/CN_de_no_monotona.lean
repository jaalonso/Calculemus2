-- CN_de_no_monotona.lean
-- Si f no es monótona, entonces ∃x∃y[x ≤ y ∧ f(y) < f(x)]​.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f no es monótona, entonces existen x, y tales que
-- x ≤ y y f(y) < f(x).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas.
--    ¬(∀x)P(x) ↔ (∃ x)¬P(x)                                         (L1)
--    ¬(p → q) ↔ p ∧ ¬q                                              (L2)
--    (∀a, b ∈ ℝ)[¬b ≤ a → a < b]                                    (L3)
--
-- Por la definición de función monótona,
--    ¬(∀x)(∀y)[x ≤ y → f(x) ≤ f(y)]
-- Aplicando L1 se tiene
--    (∃x)¬(∀y)[x ≤ y → f(x) ≤ f(y)]
-- Sea a tal que
--    ¬(∀y)[a ≤ y → f(a) ≤ f(y)]
-- Aplicando L1 se tiene
--    (∃y)¬[a ≤ y → f(a) ≤ f(y)]
-- Sea b tal que
--    ¬[a ≤ b → f(a) ≤ f(b)]
-- Aplicando L2 se tiene que
--    a ≤ b ∧ ¬(f(a) ≤ f(b))
-- Aplicando L3 se tiene que
--    a ≤ b ∧ f(b) < f(a)
-- Por tanto,
--    (∃x,y)[x ≤ y ∧ f(y) < f(x)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬Monotone f)
  : ∃ x y, x ≤ y ∧ f y < f x :=
by
  have h1 : ¬∀ x y, x ≤ y → f x ≤ f y := h
  have h2 : ∃ x, ¬(∀ y, x ≤ y → f x ≤ f y) := not_forall.mp h1
  rcases h2 with ⟨a, ha : ¬∀ y, a ≤ y → f a ≤ f y⟩
  have h3 : ∃ y, ¬(a ≤ y → f a ≤ f y) := not_forall.mp ha
  rcases h3 with ⟨b, hb : ¬(a ≤ b → f a ≤ f b)⟩
  have h4 : a ≤ b ∧ ¬(f a ≤ f b) := Classical.not_imp.mp hb
  have h5 : a ≤ b ∧ f b < f a := ⟨h4.1, lt_of_not_le h4.2⟩
  use a, b
  -- ⊢ a ≤ b ∧ f b < f a

-- 2ª demostración
-- ===============

example
  (h : ¬Monotone f)
  : ∃ x y, x ≤ y ∧ f y < f x :=
by
  simp only [Monotone] at h
  -- h : ¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b
  push_neg at h
  -- h : Exists fun ⦃a⦄ => Exists fun ⦃b⦄ => a ≤ b ∧ f b < f a
  exact h

-- Lemas usados
-- ============

-- variable {α : Type _}
-- variable (P : α → Prop)
-- variable (p q : Prop)
-- variable (a b : ℝ)
-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
-- #check (not_imp : ¬(p → q) ↔ p ∧ ¬q)
-- #check (lt_of_not_le : ¬b ≤ a → a < b)
