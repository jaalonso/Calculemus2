-- Para_todo_no_de_no_existe.lean
-- Si ¬(∃x)P(x), entonces (∀x)¬P(x).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si ¬(∃x)P(x), entonces (∀x)¬P(x).
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y un elemento cualquiera. Tenemos que demostrar ¬P(y). Para ello,
-- supongamos que P(y). Entonces, (∃x)P(x) que es una contradicción con
-- la hipótesis,

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {α : Type _}
variable (P : α → Prop)

-- 1ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  existsi y
  -- ⊢ P y
  exact h1

-- 2ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  use y

-- 3ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  apply h
  -- ⊢ ∃ x, P x
  exact ⟨y, h1⟩

-- 4ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  intros y h1
  -- y : α
  -- h1 : P x
  -- ⊢ False
  exact h ⟨y, h1⟩

-- 5ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
fun y h1 ↦ h ⟨y, h1⟩

-- 6ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by
  push_neg at h
  exact h

-- 7ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
not_exists.mp h

-- 8ª demostración
-- ===============

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by aesop

-- Lemas usados
-- ============

-- #check (not_exists : (¬∃ x, P x) ↔ ∀ (x : α), ¬P x)
