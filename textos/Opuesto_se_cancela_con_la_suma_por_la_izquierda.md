---
Título: Si R es un anillo y a, b ∈ R, entonces -a + (a + b) = b
Autor:  José A. Alonso
---

En Lean4, se declara que R es un anillo mediante la expresión
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

Demostrar que si R es un anillo, entonces
<pre lang="text">
   ∀ a, b : R, -a + (a + b) = b
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

example : -a + (a + b) = b :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   -a + (a + b) &= (-a + a) + b    &&\text{[por la asociativa]} \\
                &= 0 + b           &&\text{[por inverso por la izquierda]} \\
                &= b               &&\text{[por cero por la izquierda]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
-- 1ª demostración
example : -a + (a + b) = b :=
calc -a + (a + b) = (-a + a) + b := by rw [← add_assoc]
                _ = 0 + b        := by rw [add_left_neg]
                _ = b            := by rw [zero_add]

-- 2ª demostración
example : -a + (a + b) = b :=
by
  rw [←add_assoc]
  rw [add_left_neg]
  rw [zero_add]

-- 3ª demostración
example : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]

-- 4ª demostración
example : -a + (a + b) = b :=
by exact neg_add_cancel_left a b

-- 5ª demostración
example : -a + (a + b) = b :=
  neg_add_cancel_left a b

-- 6ª demostración
example : -a + (a + b) = b :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Opuesto_se_cancela_con_la_suma_por_la_izquierda.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 10.</li>
</ul>
