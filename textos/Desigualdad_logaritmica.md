---
Título: En ℝ, si a ≤ b, entonces log(1+e^a) ≤ log(1+e^b)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\) y \(b\) son números reales tales que
\(a \leq b\), entonces
\[\log(1+e^a) \leq \log(1+e^b)\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b : ℝ)

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]

Por la monotonía del logaritmo, basta demostrar que
\begin{align}
   &0 < 1 + e^a               \tag{1} \\
   &1 + e^a \leq 1 + e^b      \tag{2}
\end{align}

La (1), por la suma de positivos, se reduce a
\begin{align}
   &0 < 1                       \tag{1.1} \\
   &0 < e^a                     \tag{1.2}
\end{align}
La (1.1) es una propiedad de los números naturales y la (1.2) de la
función exponencial.

<div>La (2), por la monotonía de la suma, se reduce a
\[e^a \leq e^b\]
que, por la monotonía de la exponencial, se reduce a
\[a \leq b\]
que es la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b : ℝ)

-- 1ª demostración
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  have h1 : (0 : ℝ) < 1 :=
    zero_lt_one
  have h2 : 0 < exp a :=
    exp_pos a
  have h3 : 0 < 1 + exp a :=
    add_pos h1 h2
  have h4 : exp a ≤ exp b :=
    exp_le_exp.mpr h
  have h5 : 1 + exp a ≤ 1 + exp b :=
    add_le_add_left h4 1
  show log (1 + exp a) ≤ log (1 + exp b)
  exact log_le_log' h3 h5

-- 2ª demostraciṕn
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  apply log_le_log'
  { apply add_pos
    { exact zero_lt_one }
    { exact exp_pos a }}
  { apply add_le_add_left
    exact exp_le_exp.mpr h }
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Desigualdad_logaritmica.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 15.</li>
</ul>
