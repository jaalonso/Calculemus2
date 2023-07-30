---
Título: Si R es un anillo y a, b ∈ R, entonces a - b = a + -b
Autor:  José A. Alonso
---

[mathjax]
Demostrar con Lean4 que si \(R\) es un anillo y \(a, b \in R\), entonces
\[a - b = a + -b\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

example : a - b = a + -b :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Por la definición de la resta.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

example : a - b = a + -b :=
-- by exact?
sub_eq_add_neg a b
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Resta_igual_suma_opuesto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
