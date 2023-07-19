---
Título: Si a + b = c, entonces (a + b)(a + b) = ac + bc
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a, b y c son números reales tales que
<pre lang="text">
   a + b = c,
</pre>
entonces
<pre lang="text">
   (a + b) * (a + b) = a * c + b * c
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   (a + b)(a + b)
   &= (a + b)c        &&\text{[por la hipótesis]}   \\
   &= ac + bc         &&\text{[por la distributiva]}
\end{align}

<b>Demostraciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

-- 1ª demostración
example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
calc
  (a + b) * (a + b)
    = (a + b) * c   := by exact congrArg (HMul.hMul (a + b)) h
  _ = a * c + b * c := by rw [add_mul]

-- 2ª demostración
example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
by
  nth_rewrite 2 [h]
  rw [add_mul]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sia%2Bb_eq_c_entonces_(a%2Bb)(a%2Bb)_eq_ac%2Bbc.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 9.</li>
</ul>
