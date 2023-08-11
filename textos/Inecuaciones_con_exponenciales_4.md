---
Título: En ℝ, si a ≤ b entonces c - e^b ≤ c - e^a
Autor:  José A. Alonso
---

Sean \(a\), \(b\) y \(c\) números reales. Demostrar con Lean4 que si \(a
\leq b\), entonces
\[c - e^b \leq c - e^a\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b c : ℝ)

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Aplicando la monotonía de la exponencial a la hipótesis, se tiene
\[e^a \leq e^b\]
y, restando de \(c\), se invierte la desigualdad
\[c - e^b ≤ c - e^a\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b c : ℝ)

-- 1ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   have h1 : exp a ≤ exp b :=
     exp_le_exp.mpr h
   show c - exp b ≤ c - exp a
   exact sub_le_sub_left h1 c

-- 2ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   apply sub_le_sub_left _ c
   apply exp_le_exp.mpr h

-- 3ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sub_le_sub_left (exp_le_exp.mpr h) c

-- 4ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inecuaciones_con_exponenciales_4.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 16.</li>
</ul>
