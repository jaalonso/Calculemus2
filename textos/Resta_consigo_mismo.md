---
Título: Si R es un anillo y a ∈ R, entonces a - a = 0
Autor:  José A. Alonso
---

[mathjax]
Demostrar con Lean4 que si \(R\) es un anillo y \(a \in R\), entonces
\[a - a = 0\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
variable {R : Type _} [Ring R]
variable (a : R)

example : a - a = 0 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Por la siguiente cadena de igualdades:
\begin{align}
   a - a &= a + -a    &&\text{[por definición de resta]} \\
         &= 0         &&\text{[por suma con opuesto]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
example : a - a = 0 :=
calc
  a - a = a + -a := by rw [sub_eq_add_neg a a]
      _ = 0      := by rw [add_right_neg]

-- 2ª demostración
example : a - a = 0 :=
sub_self a

-- 3ª demostración
example : a - a = 0 :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Resta_consigo_mismo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
