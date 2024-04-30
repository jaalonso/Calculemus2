---
title: Imagen de la interseccion general mediante aplicaciones inyectivas
date: 2024-04-29 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \(f\) es inyectiva, entonces
\[⋂ᵢf[Aᵢ] ⊆ f[⋂ᵢAᵢ] \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set Function

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(y ∈ ⋂ᵢf[Aᵢ]\). Entonces,
\begin{align}
   & (∀i ∈ I)y ∈ f[Aᵢ]  \tag{1} \\
   & y ∈ f[Aᵢ]
\end{align}
Por tanto, existe un \(x ∈ Aᵢ\) tal que
\[ f(x) = y \tag{2} \]

Veamos que \(x ∈ ⋂ᵢAᵢ\). Para ello, sea j ∈ I. Por (1),
   y ∈ f[Aⱼ]
Luego, existe un z tal que
\begin{align}
   z ∈ Aⱼ                                                         (3)
   f(z) = y
\end{align}
Pot (2),
   f(x) = f(z)
y, por ser f inyectiva,
   x = z
y, Por (3),
   x ∈ Aⱼ

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/???).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
</pre>
