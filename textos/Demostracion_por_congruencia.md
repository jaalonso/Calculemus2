---
Título: En ℝ, |a| = |a - b + b|
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), \\(|a| = |a - b + b|\\)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (a b : ℝ)

example
  : |a| = |a - b + b| :=
by sorry
</pre>
<!--more-->

<h2>Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  : |a| = |a - b + b| :=
by
  congr
  -- a = a - b + b
  ring

-- Comentario: La táctica congr sustituye una conclusión de la forma
-- A = B por las igualdades de sus subtérminos que no no iguales por
-- definición. Por ejemplo, sustituye la conclusión (x * f y = g w * f z)
-- por las conclusiones (x = g w) y (y = z).

-- 2ª demostración
-- ===============

example
  (a b : ℝ)
  : |a| = |a - b + b| :=
by { congr ; ring }

-- 3ª demostración
-- ===============

example
  (a b : ℝ)
  : |a| = |a - b + b| :=
by ring_nf
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Demostracion_por_congruencia.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 41.</li>
</ul>
