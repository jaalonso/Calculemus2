---
Título: Si R es un anillo y a ∈ R, entonces -(-a) = a
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a ∈ R, entonces
<pre lang="text">
   -(-a) = a
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a : R}

example : -(-a) = a :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Es consecuencia de las siguiente propiedades demostradas en ejercicios anteriores:
\begin{align}
 &\forall a \ b \in R, a + b = 0 \to -a = b \\
 &\forall a \in R, -a + a = 0
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a : R}

-- 1ª demostración
example : -(-a) = a :=
by
  have h1 : -a + a = 0 := add_left_neg a
  show -(-a) = a
  exact neg_eq_of_add_eq_zero_right h1

-- 2ª demostración
example : -(-a) = a :=
by
  apply neg_eq_of_add_eq_zero_right
  rw [add_left_neg]

-- 3ª demostración
example : -(-a) = a :=
neg_neg a

-- 4ª demostración
example : -(-a) = a :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Opuesto_del_opuesto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
