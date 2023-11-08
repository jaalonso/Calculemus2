---
Título: Si f es monótona y f(a) < f(b), entonces a < b.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) es monótona y \\(f(a) < f(b)\\), entonces \\(a < b\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usaremos los lemas
\\begin{align}
   &a ≱ b → a < b \\tag{L1} \\\\
   &a ≥ b → a ≮ b \\tag{L2}
\\end{align}

Por el lema L1, basta demostrar que \\(a ≱ b\\). Lo haremos  reducción al absurdo. Para ello, supongamos que \\(a ≥ b\\). Como \\(f\\) es monótona, se tiene \\(f(a) ≥ f(b)\\) y, aplicando el lema L2, \\(f(a) ≮ f(b)\\), que contradice a la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  have h4 : f a ≥ f b := h1 h3
  have h5 : ¬ f a < f b := not_lt_of_ge h4
  exact h5 h2

-- 2ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  have h5 : ¬ f a < f b := not_lt_of_ge (h1 h3)
  exact h5 h2

-- 3ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  exact (not_lt_of_ge (h1 h3)) h2

-- 4ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  exact fun h3 ↦ (not_lt_of_ge (h1 h3)) h2

-- 5ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
lt_of_not_ge (fun h3 ↦ (not_lt_of_ge (h1 h3)) h2)

-- Lemas usados
-- ============

-- #check (lt_of_not_ge : ¬ a ≥ b → a < b)
-- #check (not_lt_of_ge : a ≥ b → ¬ a < b)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CN_de_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
