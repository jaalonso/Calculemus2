---
Título: (a + b) * (c + d) = a * c + a * d + b * c + b * d
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a, b, c y d son números reales, entonces
<pre lang="text">
   (a + b) * (c + d) = a * c + a * d + b * c + b * d
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- 1ª demostración
example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
    = a * (c + d) + b * (c + d)       := by rw [add_mul]
  _ = a * c + a * d + b * (c + d)     := by rw [mul_add]
  _ = a * c + a * d + (b * c + b * d) := by rw [mul_add]
  _ = a * c + a * d + b * c + b * d   := by rw [←add_assoc]

-- 2ª demostración
example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
    = a * (c + d) + b * (c + d)       := by ring
  _ = a * c + a * d + b * (c + d)     := by ring
  _ = a * c + a * d + (b * c + b * d) := by ring
  _ = a * c + a * d + b * c + b * d   := by ring

-- 3ª demostración
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- 4ª demostración
example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by
   rw [add_mul]
   rw [mul_add]
   rw [mul_add]
   rw [← add_assoc]

-- 5ª demostración
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by rw [add_mul, mul_add, mul_add, ←add_assoc]
</pre>

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 8.
