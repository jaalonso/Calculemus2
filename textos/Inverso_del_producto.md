---
Título: Si G es un grupo y a, b ∈ G, entonces (ab)⁻¹ = b⁻¹a⁻¹
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(G\) es un grupo y \(a, b \in G\), entonces \((ab)^{-1} = b^{-1}a^{-1}\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Teniendo en cuenta la propiedad
   \[∀ a b ∈ R, ab = 1 → a⁻¹ = b,\]
basta demostrar que
   \[(a·b)·(b⁻¹·a⁻¹) = 1.\]
La identidad anterior se demuestra mediante la siguiente cadena de
igualdades
\begin{align}
   (a·b)·(b⁻¹·a⁻¹) &= a·(b·(b⁻¹·a⁻¹))   &&\text{[por la asociativa]} \\
                   &= a·((b·b⁻¹)·a⁻¹)   &&\text{[por la asociativa]} \\
                   &= a·(1·a⁻¹)         &&\text{[por producto con inverso]} \\
                   &= a·a⁻¹             &&\text{[por producto con uno]} \\
                   &= 1                 &&\text{[por producto con
                   inverso]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

lemma aux : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
calc
  (a * b) * (b⁻¹ * a⁻¹)
    = a * (b * (b⁻¹ * a⁻¹)) := by rw [mul_assoc]
  _ = a * ((b * b⁻¹) * a⁻¹) := by rw [mul_assoc]
  _ = a * (1 * a⁻¹)         := by rw [mul_right_inv]
  _ = a * a⁻¹               := by rw [one_mul]
  _ = 1                     := by rw [mul_right_inv]

-- 1ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  exact inv_eq_of_mul_eq_one_right h1

-- 3ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  simp [h1]

-- 4ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  simp [h1]

-- 5ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  apply inv_eq_of_mul_eq_one_right
  rw [aux]

-- 6ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by exact mul_inv_rev a b

-- 7ª demostración
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inverso_del_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
