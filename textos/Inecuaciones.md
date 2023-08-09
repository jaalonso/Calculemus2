---
Título: En ℝ, si 2a ≤ 3b, 1 ≤ a y c = 2, entonces c + a ≤ 5b
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\), \(b\) y \(c\) son números reales tales que \(2a \leq 3b\), \(1 \leq a\) y \(c = 2\), entonces \(c + a \leq 5b\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de desigualdades
\begin{align}
   c + a &= 2 + a         &&\text{[por la hipótesis 3 (\(c = 2\))]} \\
         &\leq 2·a + a    &&\text{[por la hipótesis 2 (\(1 \leq a\))]} \\
         &= 3·a           \\
         &\leq 9/2·b      &&\text{[por la hipótesis 1 (\(2·a \leq 3·b\))]} \\
         &\leq 5·b
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b c : ℝ)

-- 1ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
calc
  c + a = 2 + a     := by rw [h3]
      _ ≤ 2 * a + a := by linarith only [h2]
      _ = 3 * a     := by linarith only []
      _ ≤ 9/2 * b   := by linarith only [h1]
      _ ≤ 5 * b     := by linarith

-- 2ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
by linarith
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inecuaciones.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 14.</li>
</ul>
