---
Título: En ℝ, y > x^2 ⊢ y > 0 ∨ y < -1
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), \\(y > x^2 ⊢ y > 0 ∨ y < -1\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usando el lema
\\[ (∀ x ∈ ℝ)[x² ≥ 0] \\]
se tiene que
\\begin{align}
   y &> x² &&\\text{[por hipótesis]} \\\\
     &≥ 0  &&\\text{[por el lema]}
\\end{align}
Por tanto, \\(y > 0\\) y, al verificar la primera parte de la diyunción, se verifica la disyunción.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  have h1 : y > 0 := by
    calc y > x^2 := h
         _ ≥ 0   := pow_two_nonneg x
  show y > 0 ∨ y < -1
  exact Or.inl h1

-- 2ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  calc y > x^2 := h
       _ ≥ 0   := pow_two_nonneg x

-- 3ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  linarith [pow_two_nonneg x]

-- 4ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by { left ; linarith [pow_two_nonneg x] }

-- Lema usado
-- ==========

-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Introduccion_de_la_disyuncion_1.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
