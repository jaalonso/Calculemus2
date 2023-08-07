---
Título: En ℝ, si a ≤ b, b < c, c ≤ d y d < e, entonces a < e.
Autor:  José A. Alonso
---

[mathjax]
Demostrar con Lean4 que si \(a\), \(b\), \(c\), \(d\) y \(e\) son números reales tales  \(a \leq b\), \(b < c\), \(c \leq d\) y \(d < e\), entonces \(a < e\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b c d e : ℝ)

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

<b>1ª demostración en LN</b>

Por la siguiente cadena de desigualdades
\begin{align}
   a &\leq b    &&\text{[por la hipótesis 1 (\(a \leq b\))]} \\
     &< c       &&\text{[por la hipótesis 2 (\(b < c\))]} \\
     &\leq d    &&\text{[por la hipótesis 3 (\(c \leq d\))]} \\
     &< e       &&\text{[por la hipótesis 4 (\(d < e\))]}
\end{align}

<b>2ª demostración en LN</b>

A partir de las hipótesis 1 (\(a \leq b\)) y 2 (\(b < c\)) se tiene
\[a < c\]
que, junto la hipótesis 3 (\(c \leq d\)) da
\[a < d\]
que, junto la hipótesis 4 (\(d < e\)) da
\[a < e.\]

<b>3ª demostración en LN</b>

Demostrar \(a < e\), por la hipótesis 1 (\(a \leq b\)) se reduce a
\[b < e\]
que, por la hipótesis 2 (\(b < c\)), se reduce a
\[c < e\]
que, por la hipótesis 3 (\(c \leq d\)), se reduce a
\[d < e\]
que es cierto, por la hipótesis 4.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b c d e : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
calc
  a ≤ b := h1
  _ < c := h2
  _ ≤ d := h3
  _ < e := h4

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by
  have h5 : a < c := lt_of_le_of_lt h1 h2
  have h6 : a < d := lt_of_lt_of_le h5 h3
  show a < e
  exact lt_trans h6 h4

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by
  apply lt_of_le_of_lt h1
  apply lt_trans h2
  apply lt_of_le_of_lt h3
  exact h4

-- El desarrollo de la prueba es
--
--    a b c d e : ℝ,
--    h1 : a ≤ b,
--    h2 : b < c,
--    h3 : c ≤ d,
--    h4 : d < e
--    ⊢ a < e
-- apply lt_of_le_of_lt h1,
--    ⊢ b < e
-- apply lt_trans h2,
--    ⊢ c < e
-- apply lt_of_le_of_lt h3,
--    ⊢ d < e
-- exact h4,
--    no goals

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by linarith
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cadena_de_desigualdades.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 14.</li>
</ul>
