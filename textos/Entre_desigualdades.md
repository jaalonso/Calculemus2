---
Título: En ℝ, x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que. en \\(ℝ\\), \\(x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos que
\\begin{align}
   x ≤ y \\tag{1} \\\\
   x ≠ y \\tag{2}
\\end{align}
Entonces, se tiene \\(x ≤ y\\) (por (1)) y, para probar \\(y ≰ x\\), supongamos que
\\[ y ≤ x \\tag{3}\\]
Aplicando la propiedad antimétrica a (1) y (3), se obtiene que \\(x = y\\), en contradicción con (2).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    have h4 : x = y := le_antisymm h1 h3
    show False
    exact h2 h4

-- 2ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    rintro h3 : y ≤ x
    -- ⊢ False
    show False
    exact h2 (le_antisymm h1 h3)

-- 3ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  constructor
  . show x ≤ y
    exact h1
  . show ¬ y ≤ x
    exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 4ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 5ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
  fun ⟨h1, h2⟩ ↦ ⟨h1, fun h3 ↦ h2 (le_antisymm h1 h3)⟩

-- 6ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1 : x ≤ y, h2 : x ≠ y⟩
  use h1
  exact fun h3 ↦ h2 (le_antisymm h1 h3)

-- 7ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
by
  rintro ⟨h1, h2⟩
  -- h1 : x ≤ y
  -- h2 : x ≠ y
  -- ⊢ x ≤ y ∧ ¬y ≤ x
  use h1
  -- ¬y ≤ x
  contrapose! h2
  -- h2 : y ≤ x
  -- ⊢ x = y
  apply le_antisymm h1 h2

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Entre_desigualdades.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 36.</li>
</ul>
