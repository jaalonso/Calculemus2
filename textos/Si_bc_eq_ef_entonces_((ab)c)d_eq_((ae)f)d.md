---
Título: Si bc = ef, entonces ((ab)c)d = ((ae)f)d
Autor:  José A. Alonso
---

Demostrar con Lean4 que si bc = ef, entonces ((ab)c)d = ((ae)f)d.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   ((ab)c)d
   &= (a(bc))d    &&\text{[por la asociativa]} \\
   &= (a(ef))d    &&\text{[por la hipótesis]}  \\
   &= ((ae)f)d    &&\text{[por la asociativa]}
\end{align}

<b>Demostraciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
calc
  ((a * b) * c) * d
    = (a * (b * c)) * d := by rw [mul_assoc a]
  _ = (a * (e * f)) * d := by rw [h]
  _ = ((a * e) * f) * d := by rw [←mul_assoc a]

-- 2ª demostración
example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by
  rw [mul_assoc a]
  rw [h]
  rw [←mul_assoc a]

-- 3ª demostración
example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by
  rw [mul_assoc a, h, ←mul_assoc a]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Si_bc_eq_ef_entonces_((ab)c)d_eq_((ae)f)d.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 6.</li>
</ul>
