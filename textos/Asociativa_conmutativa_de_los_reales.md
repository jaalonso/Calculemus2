---
Título: Asociativa conmutativa de los reales.
Autor:  José A. Alonso
---

Demostrar con Lean4 que los números reales tienen la siguiente propiedad
<pre lang="text">
(a * b) * c = b * (a * c)
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
sorry
</pre>

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align*}
(ab)c &= (ba)c   &&\text{[por la conmutativa]} \\
      &= b(ac)   &&\text{[por la asociativa]}
\end{align*}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ)
  : (a * b) * c = b * (a * c) :=
calc
  (a * b) * c = (b * a) * c := by rw [mul_comm a b]
            _ = b * (a * c) := by rw [mul_assoc b a c]

-- 2ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- 3ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
by ring
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Asociativa_conmutativa_de_los_reales.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 5.</li>
</ul>
