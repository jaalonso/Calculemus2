---
Título: En los anillos, 1 + 1 = 2
Autor:  José A. Alonso
---

Demostrar con Lean4 que En los anillos, \(1 + 1 = 2\)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic
variable {R : Type _} [Ring R]

example : 1 + 1 = (2 : R) :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por cálculo.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic
variable {R : Type _} [Ring R]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example : 1 + 1 = (2 : R) :=
by norm_num

-- 2ª demostración
example : 1 + 1 = (2 : R) :=
one_add_one_eq_two
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Uno_mas_uno_es_dos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
