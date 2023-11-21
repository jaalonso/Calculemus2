---
Título: P → ¬¬P.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que \\(P → ¬¬P\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable (P : Prop)

example
  (h : P)
  : ¬¬P :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos \\(¬P\\). Entonces, tenemos una contradicción con la hipótesis (\\(P\\)).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
by
  intro h1
  -- h1 : ¬P
  -- ⊢ False
  exact (h1 h)

-- 2ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
fun h1 ↦ h1 h

-- 3ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
not_not_intro h

-- 4ª demostración
-- ===============

example
  (h : P)
  : ¬ ¬ P :=
by tauto

-- Lemas usados
-- ============

-- #check (not_not_intro : P → ¬¬P)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Introduccion_doble_negacion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
