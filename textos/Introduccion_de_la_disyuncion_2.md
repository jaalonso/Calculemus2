---
Título: En ℝ, -y > x² + 1 ⊢ y > 0 ∨ y < -1.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\),
\\[ -y > x² + 1 ⊢ y > 0 ∨ y < -1 \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usaremos los siguientes lemas
\\begin{align}
   &(∀ b, c ∈ ℝ)[b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)]               \\tag{L1} \\\\
   &(∀ a ∈ ℝ)[0 ≤ a²]                                              \\tag{L2} \\\\
   &(∀ a  ∈ ℝ)[0 + a = a]                                          \\tag{L3} \\\\
   &(∀ a, b ∈ ℝ)[a < -b ↔ b < -a]                                  \\tag{L4}
\\end{align}

Se tiene
\\begin{align}
   -y &> x^2 + 1    &&\\text{[por la hipótesis]} \\\\
      &≥ 0 + 1      &&\\text{[por L1 y L2]} \\\\
      &= 1          &&\\text{[por L3]}
\\end{align}
Por tanto,
\\[ -y > 1 \\]
y, aplicando el lema L4, se tiene
\\[ y < -1 \\]
Como se verifica la segunda parte de la diyunción, se verifica la disyunción.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by
    calc -y > x^2 + 1 := by exact h
          _ ≥ 0 + 1   := add_le_add_right (pow_two_nonneg x) 1
          _ = 1       := zero_add 1
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 2ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by linarith [pow_two_nonneg x]
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 3ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1: y < -1 := by linarith [pow_two_nonneg x]
  show y > 0 ∨ y < -1
  exact Or.inr h1

-- 4ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  right
  -- ⊢ y < -1
  linarith [pow_two_nonneg x]

-- 5ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by { right ; linarith [pow_two_nonneg x] }

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (lt_neg : a < -b ↔ b < -a)
-- #check (pow_two_nonneg a : 0 ≤ a ^ 2)
-- #check (zero_add a : 0 + a = a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Introduccion_de_la_disyuncion_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>
