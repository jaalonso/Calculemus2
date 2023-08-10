---
Título: En ℝ, si 1 ≤ a y b ≤ d, entonces 2 + a + eᵇ ≤ 3a + eᵈ
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\), \(b\) y \(d\) números reales tales que \(1 \leq a\) y \(b \leq d\), entonces \(2 + a + e^b \leq 3a + e^d\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b d : ℝ)

example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
De la primera hipótesis (\(1 \leq a\)), multiplicando por \(2\), se obtiene
\[2 \leq 2a\]
y, sumando a ambos lados, se tiene
\[2 + a \leq 3a \tag{1}\]

De la hipótesis 2 (\(b \leq d\)) y de la monotonía de la función exponencial se tiene
\[e^b \leq e^d \tag{2} \]

Finalmente, de (1) y (2) se tiene
\[2 + a + e^b \leq 3a + e^d\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b d : ℝ)

-- 1ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by
  have h3 : 2 + a ≤ 3 * a := calc
    2 + a = 2 * 1 + a := by linarith only []
        _ ≤ 2 * a + a := by linarith only [h1]
        _ ≤ 3 * a     := by linarith only []
  have h4 : exp b ≤ exp d := by
    linarith only [exp_le_exp.mpr h2]
  show 2 + a + exp b ≤ 3 * a + exp d
  exact add_le_add h3 h4

-- 2ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
calc
  2 + a + exp b
    ≤ 3 * a + exp b := by linarith only [h1]
  _ ≤ 3 * a + exp d := by linarith only [exp_le_exp.mpr h2]

-- 3ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by linarith [exp_le_exp.mpr h2]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inecuaciones_con_exponenciales.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 15.</li>
</ul>
