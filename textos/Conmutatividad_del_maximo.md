---
Título: En ℝ, max(a,b) = max(b,a)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\) y \(b\) son números reales,  entonces
\(\max(a, b) = \max(b, a)\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example : max a b = max b a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Es consecuencia de la siguiente propiedad
\[\max(a, b) \leq \max(b, a) \tag{1}\]
En efecto, intercambiando las variables en (1) se obtiene
\[\max(b, a) \leq \max(a, b) \tag{2}\]
Finalmente de (1) y (2) se obtiene
\[\max(b, a) = \max(a, b)\]

Para demostrar (1), se observa que
\begin{align}
   a &\leq \max(b, a) \\
   b &\leq \max(b, a)
\end{align}
y, por tanto,
\[\max(a, b) \leq \max(b, a)\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- Lema auxiliar
-- =============

-- 1ª demostración del lema auxiliar
-- =================================

example : max a b ≤ max b a :=
by
  have h1 : a ≤ max b a := le_max_right b a
  have h2 : b ≤ max b a := le_max_left b a
  show max a b ≤ max b a
  exact max_le h1 h2

-- 2ª demostración del lema auxiliar
-- =================================

example : max a b ≤ max b a :=
by
  apply max_le
  { apply le_max_right }
  { apply le_max_left }

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux : max a b ≤ max b a :=
by exact max_le (le_max_right b a) (le_max_left b a)

-- 1ª demostración
-- ===============

example : max a b = max b a :=
by
  apply le_antisymm
  { exact aux a b}
  { exact aux b a}

-- 2ª demostración
-- ===============

example : max a b = max b a :=
le_antisymm (aux a b) (aux b a)

-- 3ª demostración
-- ===============

example : max a b = max b a :=
max_comm a b
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Conmutatividad_del_maximo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 17.</li>
</ul>
