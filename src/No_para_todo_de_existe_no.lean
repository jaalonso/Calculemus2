-- No_para_todo_de_existe_no.lean
-- Si (∃x)¬P(x), entonces ¬(∀x)P(x).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si (∃x)¬P(x), entonces ¬(∀x)P(x).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que (∀x)P(x) y tenemos que demostrar una
-- contradicción. Por hipótesis, (∃x)¬P(x). Sea y tal que
-- ¬P(y). Entonces, como (∀x)P(x), se tiene que P(y) que es una
-- contradicción con ¬P(y).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

-- 1ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  cases' h with y hy
  -- y : α
  -- hy : ¬P y
  apply hy
  -- ⊢ P y
  exact (h1 y)

-- 2ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  rcases h with ⟨y, hy : ¬P y⟩
  apply hy
  -- ⊢ P y
  exact (h1 y)

-- 3ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by
  intro h1
  -- h1 : ∀ (x : α), P x
  -- ⊢ False
  rcases h with ⟨y, hy : ¬P y⟩
  exact hy (h1 y)

-- 4ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
not_forall.mpr h

-- 5ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
not_forall_of_exists_not h

-- 6ª demostración
-- ===============

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
-- #check (not_forall_of_exists_not : (∃ x, ¬P x) → ¬∀ x, P x)
