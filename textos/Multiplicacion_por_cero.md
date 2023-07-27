---
Título: Si R es un anillo y a ∈ R, entonces a.0 = 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a ∈ R, entonces
<pre lang="text">
   a * 0 = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable (a : R)

example : a * 0 = 0 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Basta aplicar la propiedad cancelativa a
\[a.0 + a.0 = a.0 + 0\]
que se demuestra mediante la siguiente cadena de igualdades
\begin{align}
   a.0 + a.0 &= a.(0 + 0)    &&\text{[por la distributiva]} \\
             &= a.0          &&\text{[por suma con cero]} \\
             &= a.0 + 0      &&\text{[por suma con cero]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
-- ===============

example : a * 0 = 0 :=
by
  have h : a * 0 + a * 0 = a * 0 + 0 :=
    calc a * 0 + a * 0 = a * (0 + 0) := by rw [mul_add a 0 0]
                     _ = a * 0       := by rw [add_zero 0]
                     _ = a * 0 + 0   := by rw [add_zero (a * 0)]
  rw [add_left_cancel h]

-- 2ª demostración
-- ===============

example : a * 0 = 0 :=
by
  have h : a * 0 + a * 0 = a * 0 + 0 :=
    calc a * 0 + a * 0 = a * (0 + 0) := by rw [← mul_add]
                     _ = a * 0       := by rw [add_zero]
                     _ = a * 0 + 0   := by rw [add_zero]
  rw [add_left_cancel h]

-- 3ª demostración
-- ===============

example : a * 0 = 0 :=
by
  have h : a * 0 + a * 0 = a * 0 + 0 :=
    by rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- 4ª demostración
-- ===============

example : a * 0 = 0 :=
by
  have : a * 0 + a * 0 = a * 0 + 0 :=
    calc a * 0 + a * 0 = a * (0 + 0) := by simp
                     _ = a * 0       := by simp
                     _ = a * 0 + 0   := by simp
  simp

-- 5ª demostración
-- ===============

example : a * 0 = 0 :=
  mul_zero a

-- 6ª demostración
-- ===============

example : a * 0 = 0 :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Multiplicacion_por_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
