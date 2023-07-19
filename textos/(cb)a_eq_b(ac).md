---
Título: ∀ a b c ∈ ℝ, (cb)a = b(ac)
Autor:  José A. Alonso
---

Demostrar con Lean4 que los números reales tienen la siguiente propiedad
<pre lang="text">
(c * b) * a = b * (a * c)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
by sorry
</pre>

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades:
\begin{align}
   (cb)a
   &= (bc)a    &&\text{[por la conmutativa]} \\
   &= b(ca)    &&\text{[por la asociativa]} \\
   &= b(ac)    &&\text{[por la conmutativa]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a
    = (b * c) * a := by rw [mul_comm c b]
  _ = b * (c * a) := by rw [mul_assoc]
  _ = b * (a * c) := by rw [mul_comm c a]

-- 2ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]

-- 3ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by ring
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/(cb)a_eq_b(ac).lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 5.</li>
</ul>
