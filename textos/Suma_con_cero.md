---
Título: Si R es un anillo y a ∈ R, entonces a + 0 = a
Autor:  José A. Alonso
---

En Lean4, se declara que `R` es un anillo mediante la expresión
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

Demostrar que si `R` es un anillo, entonces
<pre lang="text">
   ∀ a : R, a + 0 = a
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

example : a + 0 = a :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   a + 0 &= 0 + a    &&\text{[por la conmutativa de la suma]} \\
         &= a        &&\text{[por el axioma del cero por la izquierda]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
-- 1ª demostración
example : a + 0 = a :=
calc a + 0
     = 0 + a := by rw [add_comm]
   _ = a     := by rw [zero_add]

-- 2ª demostración
example : a + 0 = a :=
by
  rw [add_comm]
  rw [zero_add]

-- 3ª demostración
example : a + 0 = a :=
by rw [add_comm, zero_add]

-- 4ª demostración
example : a + 0 = a :=
by exact add_zero a

-- 5ª demostración
example : a + 0 = a :=
  add_zero a

-- 5ª demostración
example : a + 0 = a :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_con_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 10.</li>
</ul>
