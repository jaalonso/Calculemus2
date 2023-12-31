---
Título: Si ≤ es un preorden, entonces < es irreflexiva
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(≤\\) es un preorden, entonces \\(<\\) es irreflexiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a : α)

example : ¬a < a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usará la siguiente propiedad de lo preórdenes
\\[ (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a] \\]
Con dicha propiedad, lo que tenemos que demostrar se transforma en
\\[ ¬(a ≤ a ∧ a ≰ a) \\]
Para demostrarla, supongamos que
\\[ a ≤ a ∧ a ≰ a \\]
lo que es una contradicción.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a : α)

-- 1ª demostración
-- ===============

example : ¬a < a :=
by
  rw [lt_iff_le_not_le]
  -- ⊢ ¬(a ≤ a ∧ ¬a ≤ a)
  rintro ⟨h1, h2⟩
  -- h1 : a ≤ a
  -- h2 : ¬a ≤ a
  -- ⊢ False
  exact h2 h1

-- 2ª demostración
-- ===============

example : ¬a < a :=
  irrefl a

-- Lemas usados
-- ============

-- variable (b : α)
-- #check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (irrefl a : ¬a < a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Preorden_es_irreflexivo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
