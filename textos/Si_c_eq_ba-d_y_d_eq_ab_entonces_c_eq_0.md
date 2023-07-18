---
Título: Si c = ba-d y d = ab, entonces c = 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a, b, c y d son números reales tales
<pre lang="text">
   c = b * a - d
   d = a * b
</pre>
entonces
<pre lang="text">
   c = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
by sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
calc
  c = b * a - d     := by rw [h1]
  _ = a * b - d     := by rw [mul_comm]
  _ = a * b - a * b := by rw [h2]
  _ = 0             := by rw [sub_self]

-- 2ª demostración
example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
by
  rw [h1]
  rw [mul_comm]
  rw [h2]
  rw [sub_self]
</pre>

Se puede interactuar con las pruebas anteriores en <a href="https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fjaalonso%2FCalculemus2%2Fmain%2Fsrc%2FSi_c_eq_ba-d_y_d_eq_ab_entonces_c_eq_0.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

+ J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 7.
