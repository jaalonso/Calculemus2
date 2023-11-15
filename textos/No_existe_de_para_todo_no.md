---
Título: Si (∀x)¬P(x), entonces ¬(∃x)P(x).
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\((∀x)¬P(x)\\), entonces \\(¬(∃x)P(x)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

example
  (h : ∀ x, ¬ P x)
  : ¬ ∃ x, P x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos que \\((∃x)P(x)\\). Sea \\(y\\) tal que \\(P(y)\\). Puesto que \\((∀x)¬P)x)\\), se tiene que \\(¬P(y)\\) que es una contradicción con \\(P(y)\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
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
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/No_existe_de_para_todo_no.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
