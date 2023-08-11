---
Título: En ℝ, 2ab ≤ a² + b²
Autor:  José A. Alonso
---

Sean \(a\) y \(b\) números reales. Demostrar con Lean4 que
\[2ab ≤ a^2 + b^2\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example : 2*a*b ≤ a^2 + b^2 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Puesto que los cuadrados son positivos, se tiene
\[(a - b)^2 ≥ 0\]
Desarrollando el cuadrado, se obtiene
\[a^2 - 2ab + b^2 ≥ 0\]
Sumando 2ab a ambos lados, queda
\[a^2 + b^2 ≥ 2ab\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- 1ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h1 : 0 ≤ (a - b)^2         := sq_nonneg (a - b)
  have h2 : 0 ≤ a^2 - 2*a*b + b^2 := by linarith only [h1]
  show 2*a*b ≤ a^2 + b^2
  linarith

-- 2ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2                 := (sub_sq a b).symm
       _ ≥ 0                         := sq_nonneg (a - b) }
  calc 2*a*b
       = 2*a*b + 0                   := (add_zero (2*a*b)).symm
     _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
     _ = a^2 + b^2                   := by ring

-- 3ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2       := (sub_sq a b).symm
       _ ≥ 0               := sq_nonneg (a - b) }
  linarith only [h]

-- 4ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
-- by apply?
two_mul_le_add_sq a b
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Doble_me_suma_cuadrados.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 16.</li>
</ul>
