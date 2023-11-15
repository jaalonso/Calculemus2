-- No_existe_de_para_todo_no.lean
-- Si (∀x)¬P(x), entonces ¬(∃x)P(x).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si (∀x)¬P(x), entonces ¬(∃x)P(x).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que (∃x)P(x). Sea y tal que P(y). Puesto que (∀x)¬P(x), se
-- tiene que ¬P(y) que es una contradicción con P(y).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

-- 1ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  intro h1
  -- h1 : ∃ x, P x
  -- ⊢ False
  rcases h1 with ⟨y, hy : P y⟩
  have h2 : ¬P y := h y
  exact h2 hy

-- 2ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  intro h1
  -- h1 : ∃ x, P x
  -- ⊢ False
  rcases h1 with ⟨y, hy : P y⟩
  exact (h y) hy

-- 3ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by
  rintro ⟨y, hy : P y⟩
  exact (h y) hy

-- 4ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
fun ⟨y, hy⟩ ↦ (h y) hy

-- 5ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
not_exists_of_forall_not h

-- 6ª demostración
-- ===============

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by aesop

-- Lemas usados
-- ============

-- variable (q : Prop)
-- #check (not_exists_of_forall_not : (∀ x, P x → q) → (∃ x, P x) → q)
