---
Título: En los espacios métricos, d(x,y) ≥ 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los espacios métricos, \(d(x,y) ≥ 0\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Topology.MetricSpace.Basic
variable {X : Type _} [MetricSpace X]
variable (x y : X)

example : 0 ≤ d x y :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usarán los siguientes lemas:
\begin{align}
   &0 ≤ ab → 0 < b → 0 ≤ a   \tag{L1} \\
   &d(x,x) = 0               \tag{L2} \\
   &d(x,z) ≤ d(x,y) + d(y,z) \tag{L3} \\
   &d(x,y) = d(y,x)          \tag{L4} \\
   &2a = a + a               \tag{L5} \\
   &0 < 2                    \tag{L6} \\
\end{align}

Por L5 es suficiente demostrar las siguientes desigualdades:
\begin{align}
   0 &≤ 2d(x,y) \tag{1} \\
   0 &< 2       \tag{2}
\end{align}

La (1) se demuestra por las siguiente cadena de desigualdades:
\begin{align}
   0 &= d(x,x)             &&\text{[por L2]} \\
     &≤ d(x,y) + d(y,x)    &&\text{[por L3]} \\
     &= d(x,y) + d(x,y)    &&\text{[por L4]} \\
     &= 2 d(x,y)           &&\text{[por L5]}
\end{align}

La (2) se tiene por L6.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Topology.MetricSpace.Basic
variable {X : Type _} [MetricSpace X]
variable (x y : X)

-- 1ª demostración
example : 0 ≤ dist x y :=
by
  have h1 : 0 ≤ dist x y * 2 := calc
    0 = dist x x            := (dist_self x).symm
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm x y]
    _ = dist x y * 2        := (mul_two (dist x y)).symm
  show 0 ≤ dist x y
  exact nonneg_of_mul_nonneg_left h1 zero_lt_two

-- 2ª demostración
example : 0 ≤ dist x y :=
by
  apply nonneg_of_mul_nonneg_left
  . -- 0 ≤ dist x y * 2
    calc 0 = dist x x            := by simp only [dist_self]
         _ ≤ dist x y + dist y x := by simp only [dist_triangle]
         _ = dist x y + dist x y := by simp only [dist_comm]
         _ = dist x y * 2        := by simp only [mul_two]
  . -- 0 < 2
    exact zero_lt_two

-- 3ª demostración
example : 0 ≤ dist x y :=
by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- 3ª demostración
example : 0 ≤ dist x y :=
-- by apply?
dist_nonneg

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- variable (z : X)
-- #check (dist_comm x y : dist x y = dist y x)
-- #check (dist_nonneg : 0 ≤ dist x y)
-- #check (dist_self x : dist x x = 0)
-- #check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- #check (mul_two a : a * 2 = a + a)
-- #check (nonneg_of_mul_nonneg_left : 0 ≤ a * b → 0 < b → 0 ≤ a)
-- #check (zero_lt_two : 0 < 2)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_en_espacios_metricos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 22.</li>
</ul>
