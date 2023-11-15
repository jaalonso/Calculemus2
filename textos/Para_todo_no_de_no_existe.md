---
Título: Si ¬(∃x)P(x), entonces (∀x)¬P(x).
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(¬(∃x)P(x)\\), entonces \\((∀x)¬P(x)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

example
  (h : ¬ ∃ x, P x)
  : ∀ x, ¬ P x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Sea \\(y\\) un elemento cualquiera. Tenemos que demostrar \\(¬P(y)\\). Para ello, supongamos que \\(P(y)\\). Entonces, \\((∃x)P(x)\\) que es una contradicción con la hipótesis,

<b>Demostraciones con Lean4</b>

<pre lang="lean">
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
  -- ⊢ P y
  exact h1

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
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Para_todo_no_de_no_existe.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
