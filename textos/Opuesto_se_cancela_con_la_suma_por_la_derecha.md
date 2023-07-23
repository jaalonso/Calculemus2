---
Título: Si R es un anillo y a, b ∈ R, entonces (a + b) + -b = a
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
   ∀ a, b : R, (a + b) + -b = a
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

example : (a + b) + -b = a :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
(a + b) + -b &= a + (b + -b)    &&\text{[por la asociativa]} \\
             &= a + 0           &&\text{[por suma con opuesto]} \\
             &= a               &&\text{[por suma con cero]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

-- 1ª demostración
example : (a + b) + -b = a :=
calc
  (a + b) + -b = a + (b + -b) := by rw [add_assoc]
             _ = a + 0        := by rw [add_right_neg]
             _ = a            := by rw [add_zero]

-- 2ª demostración
example : (a + b) + -b = a :=
by
  rw [add_assoc]
  rw [add_right_neg]
  rw [add_zero]

-- 3ª demostración
example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 4ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right a b

-- 5ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right _ _

-- 6ª demostración
example : (a + b) + -b = a :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Opuesto_se_cancela_con_la_suma_por_la_derecha.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
