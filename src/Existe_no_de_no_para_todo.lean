-- Existe_no_de_no_para_todo.lean
-- Si ¬(∀x)P(x), entonces (∃x)¬P(x).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si ¬(∀x)P(x), entonces (∃x)¬P(x).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por reducción al absurdo, supongamos que ¬(∃x)¬P(x). Para obtener una
-- contradicción, demostraremos la negación de la hipótesis; es decir,
-- que (∀x)P(x). Para ello, sea y un elemento cualquiera y tenemos que
-- demostrar P(y). De nuevo, lo haremos por reducción al absurdo: Para
-- ello, supongamos que ¬P(y). Entonces, se tiene que (∃x)¬P(x) en
-- contradicción con nuestro primer supuesto de ¬(∃x)¬P(x).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

-- 1ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
by
  by_contra h1
  -- h1 : ¬∃ x, ¬P x
  -- ⊢ False
  apply h
  -- ⊢ ∀ (x : α), P x
  intro y
  -- y : α
  -- ⊢ P y
  show P y
  by_contra h2
  -- h2 : ¬P y
  -- ⊢ False
  exact h1 ⟨y, h2⟩

-- 2ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
not_forall.mp h

-- 3ª demostración
-- ===============

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
