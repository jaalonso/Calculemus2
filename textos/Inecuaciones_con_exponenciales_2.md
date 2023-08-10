---
Título: En ℝ, si a ≤ b y c < d, entonces a + eᶜ + f ≤ b + eᵈ + f.
Autor:  José A. Alonso
---

Demostrar con Lean4 que \(a\), \(b\), \(c\), \(d\) y \(f\) son números reales tales que \(a \leq b\) y \(c < d\), entonces
\[a + e^c + f \leq b + e^d + f\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b c d f : ℝ)

example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by sorry
</pre>
<!--more-->

[mathjax]

<b>Demostraciones en lenguaje natural (LN)</b>

<b>1ª demostración en LN</b>

Aplicando a la hipótesis 3 (\(c < d\)) la monotonía de la exponencial, se tiene
\[e^c < e^d\]
que, junto a la hipótesis 1 (\(a \leq b\)) y la monotonía de la suma da
\[a + e^c < b + e^d\]
y, de nuevo por la monotonía de la suma, se tiene
\[a + e^c + f < b + e^d + f\]

<b>2ª demostración en LN</b>

Tenemos que demostrar que
\[(a + e^c) + f < (b + e^d) + f\]
que, por la monotonía de la suma, se reduce a las siguientes dos desigualdades:
\begin{align}
   &a + e^c < b + e^d \tag{1} \\
   &f \leq f          \tag{2}
\end{align}

La (1), de nuevo por la monotonía de la suma, se reduce a las siguientes dos:
\begin{align}
   &a \leq b     \tag{1.1} \\
   &e^c < e^d    \tag{1.2}
\end{align}

<div>La (1.1) se tiene por la hipótesis 1.

<div>La (1.2) se tiene aplicando la monotonía de la exponencial a la hipótesis 2.

La (2) se tiene por la propiedad reflexiva.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b c d f : ℝ)

-- 1ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  have h3 : exp c < exp d :=
    exp_lt_exp.mpr h2
  have h4 : a + exp c < b + exp d :=
    add_lt_add_of_le_of_lt h1 h3
  show a + exp c + f < b + exp d + f
  exact add_lt_add_right h4 f

-- 2ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  apply add_lt_add_of_lt_of_le
  { apply add_lt_add_of_le_of_lt
    { exact h1 }
    { apply exp_lt_exp.mpr
      exact h2 } }
  { apply le_refl }

-- 3ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  apply add_lt_add_of_lt_of_le
  . apply add_lt_add_of_le_of_lt h1
    apply exp_lt_exp.mpr h2
  rfl
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inecuaciones_con_exponenciales_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 15.</li>
</ul>
