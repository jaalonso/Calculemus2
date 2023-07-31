---
Título: Si G es un grupo y a ∈ G, entonces aa⁻¹ = 1
Autor:  José A. Alonso
---

En Lean4, se declara que \(G\) es un grupo mediante la expresión
<pre lang="text">
   variable {G : Type _} [Group G]
</pre>

Como consecuencia, se tiene los siguientes axiomas
<pre lang="text">
   mul_assoc :    ∀ a b c : G, a * b * c = a * (b * c)
   one_mul :      ∀ a : G, 1 * a = a
   mul_left_inv : ∀ a : G, a⁻¹ * a = 1
</pre>

Demostrar que si \(G\) es un grupo y \(a \in G\), entonces
\[aa⁻¹ = 1\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

example : a * a⁻¹ = 1 :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la siguiente cadena de igualdades
\begin{align}
   a·a⁻¹ &= 1·(a·a⁻¹)                 &&\text{[por producto con uno]} \\
         &= (1·a)·a⁻¹                 &&\text{[por asociativa]} \\
         &= (((a⁻¹)⁻¹·a⁻¹) ·a)·a⁻¹    &&\text{[por producto con inverso]} \\
         &= ((a⁻¹)⁻¹·(a⁻¹ ·a))·a⁻¹    &&\text{[por asociativa]} \\
         &= ((a⁻¹)⁻¹·1)·a⁻¹           &&\text{[por producto con inverso]} \\
         &= (a⁻¹)⁻¹·(1·a⁻¹)           &&\text{[por asociativa]} \\
         &= (a⁻¹)⁻¹·a⁻¹               &&\text{[por producto con uno]} \\
         &= 1                         &&\text{[por producto con inverso]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1ª demostración
example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by rw [one_mul]
        _ = (1 * a) * a⁻¹                := by rw [mul_assoc]
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by rw [mul_left_inv]
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by rw [← mul_assoc]
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by rw [mul_left_inv]
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by rw [mul_assoc]
        _ = (a⁻¹)⁻¹ * a⁻¹                := by rw [one_mul]
        _ = 1                            := by rw [mul_left_inv]

-- 2ª demostración
example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by simp
        _ = (1 * a) * a⁻¹                := by simp
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by simp
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by simp
        _ = (a⁻¹)⁻¹ * a⁻¹                := by simp
        _ = 1                            := by simp

-- 3ª demostración
example : a * a⁻¹ = 1 :=
by simp

-- 4ª demostración
example : a * a⁻¹ = 1 :=
by exact mul_inv_self a
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_por_inverso.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
