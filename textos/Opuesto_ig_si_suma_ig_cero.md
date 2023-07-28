---
Título: Si R es un anillo y a, b ∈ R tales que a+b=0, entonces -a=b
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a, b ∈ R tales que
<pre lang="text">
   a + b = 0
</pre>
entonces
<pre lang="text">
   -a = b
</pre>


Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b : R}

example
  (h : a + b = 0)
  : -a = b :=
sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
   -a &= -a + 0          &&\text{[por suma cero]} \\
      &= -a + (a + b)    &&\text{[por hipótesis]} \\
      &= b               &&\text{[por cancelativa]}
\end{align}

<b>2ª demostración en LN</b>

Sumando \(-a\) a ambos lados de la hipótesis, se tiene
\[-a + (a + b) = -a + 0\]
El término de la izquierda se reduce a \(b\) (por la cancelativa) y el de la derecha a \(-a\) (por la suma con cero). Por tanto, se tiene
\[b = -a\]
Por la simetría de la igualdad, se tiene
\[-a = b\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b : R}

-- 1ª demostración (basada en la 1º en LN)
example
  (h : a + b = 0)
  : -a = b :=
calc
  -a = -a + 0       := by rw [add_zero]
   _ = -a + (a + b) := by rw [h]
   _ = b            := by rw [neg_add_cancel_left]

-- 2ª demostración (basada en la 1º en LN)
example
  (h : a + b = 0)
  : -a = b :=
calc
  -a = -a + 0       := by simp
   _ = -a + (a + b) := by rw [h]
   _ = b            := by simp

-- 3ª demostración (basada en la 2º en LN)
example
  (h : a + b = 0)
  : -a = b :=
by
  have h1 : -a + (a + b) = -a + 0 := congrArg (HAdd.hAdd (-a)) h
  have h2 : -a + (a + b) = b := neg_add_cancel_left a b
  have h3 : -a + 0 = -a := add_zero (-a)
  rw [h2, h3] at h1
  exact h1.symm

-- 4ª demostración
example
  (h : a + b = 0)
  : -a = b :=
neg_eq_iff_add_eq_zero.mpr h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Opuesto_ig_si_suma_ig_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
