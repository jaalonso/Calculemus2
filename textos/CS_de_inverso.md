---
Título: Si G es un grupo y a, b ∈ G, tales que ab = 1 entonces a⁻¹ = b
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(G\) es un grupo y \(a, b \in G\) tales que \(ab = 1\) entonces \(a^{-1} = b\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

example
  (h : a * b = 1)
  : a⁻¹ = b :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se tiene a partir de la siguente cadena de igualdades
\begin{align}
   a⁻¹ &= a⁻¹·1         &&\text{[por producto por uno]} \\
       &= a⁻¹·(a·b)     &&\text{[por hipótesis]} \\
       &= (a⁻¹·a)·b     &&\text{[por asociativa]} \\
       &= 1·b           &&\text{[por producto con inverso]} \\
       &= b             &&\text{[por producto por uno]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
    _ = a⁻¹ * (a * b) := by rw [h]
    _ = (a⁻¹ * a) * b := by rw [mul_assoc]
    _ = 1 * b         := by rw [mul_left_inv]
    _ = b             := by rw [one_mul]

-- 2º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ = a⁻¹ * 1       := by simp
    _ = a⁻¹ * (a * b) := by simp [h]
    _ = (a⁻¹ * a) * b := by simp
    _ = 1 * b         := by simp
    _ = b             := by simp

-- 3º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  a⁻¹ * (a * b) := by simp [h]
    _ =  b             := by simp

-- 4º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
by exact inv_eq_of_mul_eq_one_right h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CS_de_inverso.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
