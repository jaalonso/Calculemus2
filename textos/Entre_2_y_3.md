---
Título: (∃x ∈ ℝ)[2 < x < 3]
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que \\((∃x ∈ ℝ)[2 < x < 3]\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Podemos usar el número \\(\\dfrac{5}{2}\\) y comprobar que \\(2 < \\dfrac{5}{2} < 3\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Entre_2_y_3.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 36.</li>
</ul>
