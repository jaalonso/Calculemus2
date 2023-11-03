---
Título: Si f: ℝ → ℝ es suprayectiva, entonces ∃x ∈ ℝ tal que f(x)² = 9
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(f: ℝ → ℝ\\) es suprayectiva, entonces \\(∃x ∈ ℝ\\) tal que \\(f(x)² = 9\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

example
  {f : ℝ → ℝ}
  (h : Surjective f)
  : ∃ x, (f x)^2 = 9 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Al ser \\(f\\) suprayectiva, existe un \\(y\\) tal que \\(f(y) = 3\\). Por tanto, \\(f(y)² = 9\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

open Function

example
  {f : ℝ → ℝ}
  (h : Surjective f)
  : ∃ x, (f x)^2 = 9 :=
by
  cases' h 3 with y hy
  -- y : ℝ
  -- hy : f y = 3
  use y
  -- ⊢ f y ^ 2 = 9
  rw [hy]
  -- ⊢ 3 ^ 2 = 9
  norm_num
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_de_suprayectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 31.</li>
</ul>
