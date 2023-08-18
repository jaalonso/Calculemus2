---
Título: En ℝ, min(a,b) = min(b,a)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\) y \(b\) números reales, entonces \(\min(a, b) = \min(b, a)\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example : min a b = min b a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>
[mathjax]

Es consecuencia de la siguiente propiedad
\[\min(a, b) \leq \min(b, a) \tag{1}\]
En efecto, intercambiando las variables en (1) se obtiene
\[\min(b, a) \leq \min(a, b) \tag{2}\]
Finalmente de (1) y (2) se obtiene
\[\min(b, a) = \min(a, b)\]

Para demostrar (1), se observa que
\begin{align}
   \min(a, b) &\leq b \\
   \min(a, b) &\leq a
\end{align}
y, por tanto,
\[\min(a, b) = \min(b, a)\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- Lema auxiliar
-- =============

-- 1ª demostración del lema auxiliar
-- =================================

example : min a b ≤ min b a :=
by
  have h1 : min a b ≤ b := min_le_right a b
  have h2 : min a b ≤ a := min_le_left a b
  show min a b ≤ min b a
  exact le_min h1 h2

-- 2ª demostración del lema auxiliar
-- =================================

example : min a b ≤ min b a :=
by
  apply le_min
  { apply min_le_right }
  { apply min_le_left }

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux : min a b ≤ min b a :=
by exact le_min (min_le_right a b) (min_le_left a b)

-- 1ª demostración
-- ===============

example : min a b = min b a :=
by
  apply le_antisymm
  { exact aux a b}
  { exact aux b a}

-- 2ª demostración
-- ===============

example : min a b = min b a :=
le_antisymm (aux a b) (aux b a)

-- 3ª demostración
-- ===============

example : min a b = min b a :=
min_comm a b
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Conmutatividad_del_minimo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 17.</li>
</ul>
