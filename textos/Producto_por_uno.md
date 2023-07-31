---
Título: Si G es un grupo y a ∈ G, entonces a·1 = a
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(G\) es un grupo y \(a \in G\), entonces
\[a·1 = a\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

example : a * 1 = a :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se tiene por la siguiente cadena de igualdades
\begin{align}
   a·1 &= a·(a⁻¹·a)    &&\text{[por producto con inverso]} \\
       &= (a·a⁻¹)·a    &&\text{[por asociativa]} \\
       &= 1·a          &&\text{[por producto con inverso]} \\
       &= a            &&\text{[por producto con uno]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1ª demostración
example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by rw [mul_left_inv]
      _ = (a * a⁻¹) * a := by rw [mul_assoc]
      _ = 1 * a         := by rw [mul_right_inv]
      _ = a             := by rw [one_mul]

-- 2ª demostración
example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by simp
      _ = (a * a⁻¹) * a := by simp
      _ = 1 * a         := by simp
      _ = a             := by simp

-- 3ª demostración
example : a * 1 = a :=
by simp

-- 4ª demostración
example : a * 1 = a :=
by exact mul_one a
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_por_uno.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
