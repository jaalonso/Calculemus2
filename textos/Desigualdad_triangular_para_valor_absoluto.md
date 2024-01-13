---
Título: En ℝ, |x + y| ≤ |x| + |y|.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\),
\\[ |x + y| ≤ |x| + |y| \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

example : |x + y| ≤ |x| + |y| :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usarán los siguientes lemas
\\begin{align}
    &(∀ x ∈ ℝ)[0 ≤ x → |x| = x)                          \\tag{L1} \\\\
    &(∀ a, b, c, d ∈ ℝ)[a ≤ b ∧ c ≤ d → a + c ≤ b + d]   \\tag{L2} \\\\
    &(∀ x ∈ ℝ)[x ≤ |x|]                                  \\tag{L3} \\\\
    &(∀ x ∈ ℝ)[x < 0 → |x| = -x]                         \\tag{L4} \\\\
    &(∀ x, y ∈ ℝ)[-(x + y) = -x + -y]                    \\tag{L5} \\\\
    &(∀ x ∈ ℝ)[-x ≤ |x|]                                 \\tag{L6}
\\end{align}

Se demostrará por casos según \\(x + y ≥ 0\\):

Primer caso: Supongamos que \\(x + y ≥ 0\\). Entonces,
\\begin{align}
   |x + y| &= x + y        &&\\text{[por L1]} \\\\
           &≤ |x| + |y|    &&\\text{[por L2 y L3]}
\\end{align}

Segundo caso: Supongamos que \\(x + y < 0\\). Entonces,
\\begin{align}
   |x + y| &= -(x + y)     &&\\text{[por L4]} \\\\
           &= -x + -y      &&\\text{[por L5]} \\\\
           &≤ |x| + |y|    &&\\text{[por L2 y L6]}
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| :=
by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = x + y     := by exact abs_of_nonneg h1
               _ ≤ |x| + |y| := add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = -(x + y)  := by exact abs_of_neg h2
               _ = -x + -y   := by exact neg_add x y
               _ ≤ |x| + |y| := add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    exact add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    calc -(x + y) = -x + -y    := by exact neg_add x y
                _ ≤ |x| + |y|  := add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    linarith [le_abs_self x, le_abs_self y]
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    linarith [neg_le_abs_self x, neg_le_abs_self y]

-- 3ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| :=
  abs_add x y

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- #check (abs_add x y : |x + y| ≤ |x| + |y|)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (neg_add x y : -(x + y) = -x + -y)
-- #check (neg_le_abs_self x : -x ≤ |x|)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Desigualdad_triangular_para_valor_absoluto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
