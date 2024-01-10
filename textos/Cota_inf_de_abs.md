---
Título: En ℝ, x ≤ |x|
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), \\(x ≤ |x|\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

example : x ≤ |x| :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usarán los siguientes lemas
\\begin{align}
   &(∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     \\tag{L1} \\\\
   &(∀ x, y ∈ ℝ)[x < y → x ≤ y]                                    \\tag{L2} \\\\
   &(∀ x ∈ ℝ)[x ≤ 0 → x ≤ -x]                                      \\tag{L3} \\\\
   &(∀ x ∈ ℝ)[x < 0 → |x| = -x]                                    \\tag{L4}
\\end{align}

Se demostrará por casos según \\(x ≥ 0\\):

Primer caso: Supongamos que \\(x ≥ 0\\). Entonces,
\\begin{align}
   x &≤ x      \\\\
     &= |x|    &&\\text{[por L1]}
\\end{align}

Segundo caso: Supongamos que \\(x < 0\\). Entonces, por el L2, se tiene
\\[ x ≤ 0 \\tag{1} \\]
Por tanto,
\\begin{align}
   x &≤ -x     &&\\text{[por L3 y (1)]} \\\\
     &= |x|    &&\\text{[por L4]}
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

-- 1ª demostración
-- ===============

example : x ≤ |x| :=
by
  cases' le_or_gt 0 x with h1 h2
  . -- h1 : 0 ≤ x
    show x ≤ |x|
    calc x ≤ x   := le_refl x
         _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    have h3 : x ≤ 0 := le_of_lt h2
    show x ≤ |x|
    calc x ≤ -x  := le_neg_self_iff.mpr h3
         _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : x ≤ |x| :=
by
  cases' le_or_gt 0 x with h1 h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h2 : 0 > x
    rw [abs_of_neg h2]
    -- ⊢ x ≤ -x
    apply Left.self_le_neg
    -- ⊢ x ≤ 0
    exact le_of_lt h2

-- 3ª demostración
-- ===============

example : x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h1 : 0 ≤ x
    rw [abs_of_neg h2]
    linarith

-- 4ª demostración
-- ===============

example : x ≤ |x| :=
  le_abs_self x

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (Left.self_le_neg : x ≤ 0 → x ≤ -x)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_abs_self x : x ≤ |x|)
-- #check (le_neg_self_iff : x ≤ -x ↔ x ≤ 0)
-- #check (le_of_lt : x < y → x ≤ y)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cota_inf_de_abs.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
