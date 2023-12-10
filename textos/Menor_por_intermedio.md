---
Título: Si (∃z ∈ ℝ)[x < z < y], entonces x < y.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\((∃z ∈ ℝ)[x < z < y]\\), entonces \\(x < y\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Sea \\(z\\) tal que verifica las siguientes relaciones:
\\begin{align}
   x < z \\tag{1} \\\\
   z < y \\tag{2}
\\end{align}
Aplicando la propiedad transitiva a (1) y (2) se tiene que
\\[ x < y \\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1 : x < z, h2 : z < y⟩
  show x < y
  exact lt_trans h1 h2

-- 2ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1, h2⟩
  exact lt_trans h1 h2

-- 3ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
fun ⟨_, h1, h2⟩ ↦ lt_trans h1 h2

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (lt_trans : a < b → b < c → a < c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Menor_por_intermedio.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 36.</li>
</ul>
