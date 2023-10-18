---
Título: La función (x ↦ x + c) es inyectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que la función \\(x ↦ x + c\\) es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable {c : ℝ}

example : Injective ((. + c)) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el lema
\\[ (∀ a, b, c) [a + b = c + b → a = c] \\tag{L1} \\]

Hay que demostrar que
\\[ (∀ x₁ x₂) [f(x₁) = f(x₂) → x₁ = x₂] \\]
Sean \\(x₁, x₂\\) tales que \\(f(x₁) = f(x₂)\\). Entonces,
\\[ x₁ + c = x₂ + c \\]
y, por L1, \\(x₁ = x₂\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable {c : ℝ}

-- 1ª demostración
example : Injective ((. + c)) :=
by
  intro (x1 : ℝ) (x2 : ℝ) (h1 : x1 + c = x2 + c)
  show x1 = x2
  exact add_right_cancel h1

-- 2ª demostración
example : Injective ((. + c)) :=
by
  intro x1 x2 h1
  show x1 = x2
  exact add_right_cancel h1

-- 3ª demostración
example : Injective ((. + c)) :=
  fun _ _ h ↦ add_right_cancel h

-- Lemas usados
-- ============

-- variable {a b : ℝ}
-- #check (add_right_cancel : a + b = c + b → a = c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_constante_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 28.</li>
</ul>
