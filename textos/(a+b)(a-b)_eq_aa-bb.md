---
Título: (a+b)(a-b) = a^2-b^2
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a y b son números reales, entonces
<pre lang="text">
   (a + b) * (a - b) = a^2 - b^2
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

example : (a + b) * (a - b) = a^2 - b^2 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades:
\begin{align}
(a + b)(a - b)
&= a(a - b) + b(a - b)            &&\text{[por la distributiva]} \\
&= (aa - ab) + b(a - b)           &&\text{[por la distributiva]} \\
&= (a^2 - ab) + b(a - b)          &&\text{[por def. de cuadrado]} \\
&= (a^2 - ab) + (ba - bb)         &&\text{[por la distributiva]} \\
&= (a^2 - ab) + (ba - b^2)        &&\text{[por def. de cuadrado]} \\
&= (a^2 + -(ab)) + (ba - b^2)     &&\text{[por def. de resta]} \\
&= a^2 + (-(ab) + (ba - b^2))     &&\text{[por la asociativa]} \\
&= a^2 + (-(ab) + (ba + -b^2))    &&\text{[por def. de resta]} \\
&= a^2 + ((-(ab) + ba) + -b^2)    &&\text{[por la asociativa]} \\
&= a^2 + ((-(ab) + ab) + -b^2)    &&\text{[por la conmutativa]} \\
&= a^2 + (0 + -b^2)               &&\text{[por def. de opuesto]} \\
&= (a^2 + 0) + -b^2               &&\text{[por asociativa]} \\
&= a^2 + -b^2                     &&\text{[por def. de cero]} \\
&= a^2 - b^2                      &&\text{[por def. de resta]}
\end{align}

<b>Demostraciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- 1ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by rw [add_mul]
  _ = (a * a - a * b) + b * (a - b)     := by rw [mul_sub]
  _ = (a^2 - a * b) + b * (a - b)       := by rw [← pow_two]
  _ = (a^2 - a * b) + (b * a - b * b)   := by rw [mul_sub]
  _ = (a^2 - a * b) + (b * a - b^2)     := by rw [← pow_two]
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by rw [add_assoc]
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by rw [← add_assoc
                                              (-(a * b)) (b * a) (-b^2)]
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by rw [mul_comm]
  _ = a^2 + (0 + -b^2)                  := by rw [neg_add_self (a * b)]
  _ = (a^2 + 0) + -b^2                  := by rw [← add_assoc]
  _ = a^2 + -b^2                        := by rw [add_zero]
  _ = a^2 - b^2                         := by linarith

-- 2ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by ring
  _ = (a * a - a * b) + b * (a - b)     := by ring
  _ = (a^2 - a * b) + b * (a - b)       := by ring
  _ = (a^2 - a * b) + (b * a - b * b)   := by ring
  _ = (a^2 - a * b) + (b * a - b^2)     := by ring
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by ring
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by ring
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by ring
  _ = a^2 + (0 + -b^2)                  := by ring
  _ = (a^2 + 0) + -b^2                  := by ring
  _ = a^2 + -b^2                        := by ring
  _ = a^2 - b^2                         := by ring

-- 3ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

-- 4ª demostración (por reescritura usando el lema anterior)
-- =========================================================

-- El lema anterior es
lemma aux : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- La demostración es
example : (a + b) * (a - b) = a^2 - b^2 :=
by
  rw [sub_eq_add_neg]
  rw [aux]
  rw [mul_neg]
  rw [add_assoc (a * a)]
  rw [mul_comm b a]
  rw [neg_add_self]
  rw [add_zero]
  rw [← pow_two]
  rw [mul_neg]
  rw [← pow_two]
  rw [← sub_eq_add_neg]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/(a+b)(a-b)_eq_aa-bb.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 8.</li>
</ul>
