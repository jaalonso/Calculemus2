---
Título: Si a + b = c, entonces (a + b)(a + b) = ac + bc
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a, b y c son números reales tales que
<pre lang="text">
   a + b = c,
</pre>
entonces
<pre lang="text">
   (a + b) * (a + b) = a * c + b * c
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

-- 1ª demostración
example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
calc
  (a + b) * (a + b)
    = (a + b) * c   := by exact congrArg (HMul.hMul (a + b)) h
  _ = a * c + b * c := by rw [add_mul]

-- 2ª demostración
example
  (h : a + b = c)
  : (a + b) * (a + b) = a * c + b * c :=
by
  nth_rewrite 2 [h]
  rw [add_mul]
</pre>

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 9.
