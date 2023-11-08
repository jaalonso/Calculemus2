---
Título: Si a, b ∈ ℝ tales que a ≤ b y f(b) < f(a), entonces f no es monótona.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(a, b ∈ ℝ\\) tales que \\(a ≤ b\\) y \\(f(b) < f(a)\\), entonces \\(f\\) no es monótona

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usaremos el lema
\\[ a ≥ b → a ≮ b \\tag{L1} \\]

Lo demostraremos por reducción al absurdo. Para ello, supongamos que \\(f\\) es monótona. Entonces, como \\(a ≤ b\\), se tiene \\(f(a) ≤ f(b)\\) y, por el lema L1, \\(f(b) ≮ f(a)\\), en contradicción con la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  have h4 : f a ≤ f b := h3 h1
  have h5 : ¬(f b < f a) := not_lt_of_ge h4
  exact h5 h2

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  have h5 : ¬(f b < f a) := not_lt_of_ge (h3 h1)
  exact h5 h2

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  exact (not_lt_of_ge (h3 h1)) h2

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
fun h3 ↦ (not_lt_of_ge (h3 h1)) h2

-- Lemas usados
-- ============

-- #check (not_lt_of_ge : a ≥ b → ¬a < b)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CS_de_no_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
