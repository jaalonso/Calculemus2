---
Título: Si (∃x)¬P(x), entonces ¬(∀x)P(x).
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\((∃x)¬P(x)\\), entonces \\(¬(∀x)P(x)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

example
  (h : ∃ x, ¬ P x)
  : ¬ ∀ x, P x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos que \\((∀x)P(x)\\) y tenemos que demostrar  contradicción. Por hipótesis, \\((∃x)¬P(x)\\). Sea \\(y\\) tal que \\(¬P(y)\\). Entonces, como \\((∀x)P(x)\\), se tiene \\(P(y)\\) que es una contradicción con \\(¬P(y)\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
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
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/No_para_todo_de_existe_no.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
