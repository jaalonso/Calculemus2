---
Título: En ℝ, si d ≤ f, entonces c + e^(a + d) ≤ c + e^(a + f)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\), \(c\), \(d\) y \(f\) son números
reales tales que \(d ≤ f\), entonces
\[c + e^{a + d} \leq c + e^{a + f}\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a c d f : ℝ)

example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]

<b>1ª demostración en LN</b>

De la hipótesis, por la monotonia de la suma, se tiene
\[a + d \leq a + f\]
que, por la monotonía de la exponencial, da
\[e^{a + d} \leq e^{a + f}\]
y, por la monotonía de la suma, se tiene
\[c + e^{a + d} \leq c + e^{a + f}\]

2ª demostración en LN
=====================

Tenemos que demostrar que
\[c + e^{a + d} \leq c + e^{a + f}\]
Por la monotonía de la suma, se reduce a
\[e^{a + d} \leq e^{a + f}\]
que, por la monotonía de la exponencial, se reduce a
\[a + d \leq a + f\]
que, por la monotonía de la suma, se reduce a
\[d \leq f\]
que es la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a c d f : ℝ)

-- 1ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  have h1 : a + d ≤ a + f :=
    add_le_add_left h a
  have h2 : exp (a + d) ≤ exp (a + f) :=
    exp_le_exp.mpr h1
  show c + exp (a + d) ≤ c + exp (a + f)
  exact add_le_add_left h2 c

-- 2ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  apply add_le_add_left
  apply exp_le_exp.mpr
  apply add_le_add_left
  exact h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inecuaciones_con_exponenciales_3.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 15.</li>
</ul>
