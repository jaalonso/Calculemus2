---
Título: Si R es un anillo y a, b ∈ R tales que a+b=0, entonces a=-b
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a, b ∈ R tales que
<pre lang="text">
   a + b = 0
</pre>
entonces
<pre lang="text">
   a = -b
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b : R}

example
  (h : a + b = 0)
  : a = -b :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
<b>1ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
   a &= (a + b) + -b    &&\text{[por la concelativa]} \\
     &= 0 + -b          &&\text{[por la hipótesis]} \\
     &= -b              &&\text{[por la suma con cero]}
\end{align}

<b>2ª demostración en LN</b>

Sumando \(-a\) a ambos lados de la hipótesis, se tiene
\[(a + b) + -b = 0 + -b\]
El término de la izquierda se reduce a \(a\) (por la cancelativa) y el de la derecha a \(-b\) (por la suma con cero). Por tanto, se tiene
\[a = -b\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b : R}

-- 1ª demostración (basada en la 1ª en LN)
example
  (h : a + b = 0)
  : a = -b :=
calc
  a = (a + b) + -b := by rw [add_neg_cancel_right]
  _ = 0 + -b       := by rw [h]
  _ = -b           := by rw [zero_add]

-- 2ª demostración (basada en la 1ª en LN)
example
  (h : a + b = 0)
  : a = -b :=
calc
  a = (a + b) + -b := by simp
  _ = 0 + -b       := by rw [h]
  _ = -b           := by simp

-- 3ª demostración (basada en la 1ª en LN)
example
  (h : a + b = 0)
  : a = -b :=
by
  have h1 : (a + b) + -b = 0 + -b := by rw [h]
  have h2 : (a + b) + -b = a := add_neg_cancel_right a b
  have h3 : 0 + -b = -b := zero_add (-b)
  rwa [h2, h3] at h1

-- 4ª demostración
example
  (h : a + b = 0)
  : a = -b :=
add_eq_zero_iff_eq_neg.mp h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ig_opuesto_si_suma_ig_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
