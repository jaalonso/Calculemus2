---
Título: La función x ↦ -x no es monótona creciente
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que la función \\(x ↦ -x\\) no es monótona creciente.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import src.CNS_de_no_monotona

example : ¬Monotone fun x : ℝ ↦ -x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usando el lema del ejercicio anterior que afirma que una función f no es monótona syss existen x e y tales que x ≤ y y f(x) > f(y), basta demostrar que
\\[ (∃ x, y)[x ≤ y ∧ -x > -y] \\]
Basta elegir 2 y 3 ya que
\\[ 2 ≤ 3 ∧ -2 > -3 \\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import src.CNS_de_no_monotona

example : ¬Monotone fun x : ℝ ↦ -x :=
by
  apply not_Monotone_iff.mpr
  -- ⊢ ∃ x y, x ≤ y ∧ -x > -y
  use 2, 3
  -- ⊢ 2 ≤ 3 ∧ -2 > -3
  norm_num
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_opuesta_es_no_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 37.</li>
</ul>
