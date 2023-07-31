---
Título: Si R es un anillo y a ∈ R, entonces 2a = a+a
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(R\) es un anillo y \(a \in R\), entonces
\[2a = a+a\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

example : 2 * a = a + a :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   2·a &= (1 + 1)·a    &&\text{[por la definición de 2]} \\
       &= 1·a + 1·a    &&\text{[por la distributiva]} \\
       &= a + a        &&\text{[por producto con uno]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   := by rw [one_add_one_eq_two]
      _ = 1 * a + 1 * a := by rw [add_mul]
      _ = a + a         := by rw [one_mul]

-- 2ª demostración
example : 2 * a = a + a :=
by exact two_mul a
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_por_dos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
