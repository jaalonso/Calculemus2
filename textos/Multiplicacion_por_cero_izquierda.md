---
Título: Si R es un anillo y a ∈ R, entonces 0.a = 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a ∈ R, entonces
<pre lang="text">
   0 * a = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable (a : R)

example : 0 * a = 0 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Basta aplicar la propiedad cancelativa a
\[0.a + 0.a = 0.a + 0\]
que se demuestra mediante la siguiente cadena de igualdades
\begin{align}
   0.a + 0.a &= (0 + 0).a    &&\text{[por la distributiva]} \\
             &= 0.a          &&\text{[por suma con cero]} \\
             &= 0.a + 0      &&\text{[por suma con cero]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by rw [add_mul]
                     _ = 0 * a       := by rw [add_zero]
                     _ = 0 * a + 0   := by rw [add_zero]
  rw [add_left_cancel h]

-- 2ª demostración
example : 0 * a = 0 :=
by
  have h : 0 * a + 0 * a = 0 * a + 0 :=
    by rw [←add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

-- 3ª demostración
example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 :=
    calc 0 * a + 0 * a = (0 + 0) * a := by simp
                     _ = 0 * a       := by simp
                     _ = 0 * a + 0   := by simp
  simp

-- 4ª demostración
example : 0 * a = 0 :=
by
  have : 0 * a + 0 * a = 0 * a + 0 := by simp
  simp

-- 5ª demostración
example : 0 * a = 0 :=
by simp

-- 6ª demostración
example : 0 * a = 0 :=
zero_mul a
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Multiplicacion_por_cero_izquierda.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
