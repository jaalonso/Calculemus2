---
Título: Si ¬(∀x)P(x), entonces (∃x)¬P(x).
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(¬(∀x)P(x)\\), entonces \\((∃x)¬P(x)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _}
variable (P : α → Prop)

example
  (h : ¬ ∀ x, P x)
  : ∃ x, ¬ P x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Por reducción al absurdo, supongamos que \\(¬(∃x)¬P(x)\\). Para obtener  contradicción, demostraremos la negación de la hipótesis; es  que \\((∀x)P(x)\\). Para ello, sea \\(y\\) un elemento cualquiera y tenemos que demostrar \\(P(y)\\). De nuevo, lo haremos por reducción al absurdo: Para ello, supongamos que \\(¬P(y)\\). Entonces, se tiene que \\((∃x)¬P(x)\\) en contradicción con nuestro primer supuesto de \\(¬(∃x)¬P(x)\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
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
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Existe_no_de_no_para_todo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
