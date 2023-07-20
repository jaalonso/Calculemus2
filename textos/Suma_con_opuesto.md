---
Título: Si R es un anillo y a ∈ R, entonces a + -a = 0
Autor:  José A. Alonso
---

En Lean4, se declara que \(R\) es un anillo mediante la expresión
<pre lang="text">
   variable {R : Type _} [Ring R]
</pre>
Como consecuencia, se tiene los siguientes axiomas
<pre lang="text">
   add_assoc    : ∀ a b c : R, (a + b) + c = a + (b + c)
   add_comm     : ∀ a b : R,   a + b = b + a
   zero_add     : ∀ a : R,     0 + a = a
   add_left_neg : ∀ a : R,     -a + a = 0
   mul_assoc    : ∀ a b c : R, a * b * c = a * (b * c)
   mul_one      : ∀ a : R,     a * 1 = a
   one_mul      : ∀ a : R,     1 * a = a
   mul_add      : ∀ a b c : R, a * (b + c) = a * b + a * c
   add_mul      : ∀ a b c : R, (a + b) * c = a * c + b * c
</pre>

Demostrar que si \(R\) es un anillo, entonces
<pre lang="text">
   ∀ a : R, a + -a = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

example : a + -a = 0 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   a + -a &= -a + a    &&\text{[por la conmutativa de la suma]} \\
          &= 0         &&\text{[por el axioma de inverso por la izquierda]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
-- ===============

example : a + -a = 0 :=
calc a + -a = -a + a := by rw [add_comm]
          _ = 0      := by rw [add_left_neg]

-- 2ª demostración
-- ===============

example : a + -a = 0 :=
by
  rw [add_comm]
  rw [add_left_neg]

-- 3ª demostración
-- ===============

example : a + -a = 0 :=
by rw [add_comm, add_left_neg]

-- 4ª demostración
-- ===============

example : a + -a = 0 :=
by exact add_neg_self a

-- 5ª demostración
-- ===============

example : a + -a = 0 :=
  add_neg_self a

-- 6ª demostración
-- ===============

example : a + -a = 0 :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_con_opuesto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 10.</li>
</ul>
