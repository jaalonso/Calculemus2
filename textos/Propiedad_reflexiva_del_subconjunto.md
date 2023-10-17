---
Título: Para cualquier conjunto s, s ⊆ s
Autor:  José A. Alonso
---

Demostrar con Lean4 que para cualquier conjunto \\(s\\), \\(s ⊆ s\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {α : Type _}
variable (s : Set α)

example : s ⊆ s :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Tenemos que demostrar que
\\[ (∀ x) [x ∈ s → × ∈ s] \\]
Sea \\(x\\) tal que
\\[ x ∈ s \\tag{1} \\]
Entonces, por (1), se tiene que
\\[ x ∈ s \\]
que es lo que teníamos que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

variable {α : Type _}
variable (s : Set α)

-- 1ª demostración
example : s ⊆ s :=
by
  intro x xs
  exact xs

-- 2ª demostración
example : s ⊆ s :=
  fun (x : α) (xs : x ∈ s) ↦ xs

-- 3ª demostración
example : s ⊆ s :=
  fun _ xs ↦ xs

-- 4ª demostración
example : s ⊆ s :=
  -- by exact?
  rfl.subset

-- 5ª demostración
example : s ⊆ s :=
by rfl
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_reflexiva_del_subconjunto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 27.</li>
</ul>
