---
Título: En ℝ, -x ≤ |x|
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), \\(-x ≤ |x|\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

example : -x ≤ |x| :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usarán los siguientes lemas
\\begin{align}
   &(∀ x ∈ ℝ)[0 ≤ x → -x ≤ x]                                      \\tag{L1} \\\\
   &(∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     \\tag{L2} \\\\
   &(∀ x ∈ ℝ)[x ≤ x]                                               \\tag{L3} \\\\
   &(∀ x ∈ ℝ)[x < 0 → |x| = -x]                                    \\tag{L4}
\\end{align}

Se demostrará por casos según \\(x ≥ 0\\):

Primer caso: Supongamos que \\(x ≥ 0\\). Entonces,
\\begin{align}
   -x &≤ x      &&\\text{[por L1]} \\\\
      &= |x|    &&\\text{[por L2]}
\\end{align}

Segundo caso: Supongamos que \\(x < 0\\). Entonces,
\\begin{align}
   -x &≤ -x     &&\\text{[por L3]} \\\\
      &= |x|    &&\\text{[por L4]}
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

-- 1ª demostración
-- ===============

example : -x ≤ |x| :=
by
  cases' (le_or_gt 0 x) with h1 h2
  . -- h1 : 0 ≤ x
    show -x ≤ |x|
    calc -x ≤ x   := by exact neg_le_self h1
          _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    show -x ≤ |x|
    calc -x ≤ -x  := by exact le_refl (-x)
          _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : -x ≤ |x| :=
by
  cases' (le_or_gt 0 x) with h1 h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    exact neg_le_self h1
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 3ª demostración
-- ===============

example : -x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    linarith
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 4ª demostración
-- ===============

example : -x ≤ |x| :=
  neg_le_abs_self x

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (le_refl x : x ≤ x)
-- #check (neg_le_abs_self x : -x ≤ |x|)
-- #check (neg_le_self : 0 ≤ x → -x ≤ x)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cota_inf2_de_abs.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
