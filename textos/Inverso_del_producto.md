---
title: Si G es un grupo y a, b ∈ G, entonces (ab)⁻¹ = b⁻¹a⁻¹
date: 2024-05-14 06:00:00 UTC+02:00
category: Grupos
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(G\\) es un grupo y \\(a, b \\in G\\), entonces \\((ab)^{-1} = b^{-1}a^{-1}\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
sorry
</pre>
<!--more-->

<h2>Demostración en lenguaje natural</h2>

[mathjax]
Teniendo en cuenta la propiedad
   \\[(∀ a, b ∈ G)[ab = 1 → a⁻¹ = b] \\]
basta demostrar que
   \\[(a·b)·(b⁻¹·a⁻¹) = 1.\\]
que se demuestra mediante la siguiente cadena de igualdades
\\begin{align}
   (a·b)·(b⁻¹·a⁻¹) &= a·(b·(b⁻¹·a⁻¹))   &&\\text{[por la asociativa]} \\\\
                   &= a·((b·b⁻¹)·a⁻¹)   &&\\text{[por la asociativa]} \\\\
                   &= a·(1·a⁻¹)         &&\\text{[por producto con inverso]} \\\\
                   &= a·a⁻¹             &&\\text{[por producto con uno]} \\\\
                   &= 1                 &&\\text{[por producto con
                   inverso]}
\\end{align}

<h2>Demostraciones con Lean4</h2>

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

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inverso_del_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Inverso_del_producto
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "(a * b) * (inverse b * inverse a) =
        ((a * b) * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = (a * (b * inverse b)) * inverse a"
    by (simp only: assoc)
  also have "… = (a * 1) * inverse a"
    by (simp only: right_inverse)
  also have "… = a * inverse a"
    by (simp only: right_neutral)
  also have "… = 1"
    by (simp only: right_inverse)
  finally show "a * b * (inverse b * inverse a) = 1"
    by this
qed

(* 2ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "(a * b) * (inverse b * inverse a) =
        ((a * b) * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = (a * (b * inverse b)) * inverse a"
    by (simp only: assoc)
  also have "… = (a * 1) * inverse a"
    by simp
  also have "… = a * inverse a"
    by simp
  also have "… = 1"
    by simp
  finally show "a * b * (inverse b * inverse a) = 1"
    .
qed

(* 3ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "a * b * (inverse b * inverse a) =
        a * (b * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = 1"
    by simp
  finally show "a * b * (inverse b * inverse a) = 1" .
qed

(* 4ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
  by (simp only: inverse_distrib_swap)

end

end
</pre>

<h2>Referencias</h2>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 12.</li>
</ul>
