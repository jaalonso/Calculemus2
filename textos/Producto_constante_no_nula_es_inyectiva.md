---
Título: Si c ≠ 0, entonces la función (x ↦ cx) es inyectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(c ≠ 0\\), entonces la función \\(x ↦ cx\\) es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function
variable {c : ℝ}

example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el lema
\\[ (∀ a, b, c) [a ≠ 0 → (ab = ac ↔ b = c))] \\tag{L1} \\]

Hay que demostrar que
\\[ (∀ x₁, x₂) [f(x₁) = f(x₂) → x₁ = x₂] \\]
Sean \\(x₁, x₂\\) tales que \\(f(x₁) = f(x₂)\\). Entonces,
\\[ cx₁ = cx₂ \\]
y, por L1 y puesto que \\(c ≠ 0\\), se tiene que
\\[ x₁ = x₂ \\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function
variable {c : ℝ}

-- 1ª demostración
example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
by
  intro (x1 : ℝ) (x2 : ℝ) (h1 : c * x1 = c * x2)
  show x1 = x2
  exact (mul_right_inj' h).mp h1

-- 2ª demostración
example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
fun _ _ h1 ↦ mul_left_cancel₀ h h1

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_right_inj' : a ≠ 0 → (a * b = a * c ↔ b = c))
-- #check (mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_constante_no_nula_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 28.</li>
</ul>
