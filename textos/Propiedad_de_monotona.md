---
Título: No para toda f : ℝ → ℝ monótona, (∀a,b)[f(a) ≤ f(b) → a ≤ b].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que no para toda \\(f : ℝ → ℝ\\) monótona, \\((∀a,b)[f(a) ≤ f(b) → a ≤ b]\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

example :
  ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos que
\\[ (∀f)[f \\text{ es monótona } → (∀a, b)[f(a) ≤ f(b) → a ≤ b]] \\tag{1} \\]
Sea \\(f : ℝ → ℝ\\) la función constante igual a cero (es decir,
\\[ (∀x ∈ ℝ)[f(x) = 0] \\]
Entonces, \\(f\\) es monótona y \\(f(1) ≤ f(0)\\) (ya que \\(f(1) = 0 ≤ 0 = f(0)\\)). Luego, por (1), \\(1 ≤ 0\\) que es una contradicción.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example :
  ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
by
  intro h1
  -- h1 : ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b : ℝ}, f a ≤ f b → a ≤ b
  -- ⊢ False
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have h2 : Monotone f := monotone_const
  have h3 : f 1 ≤ f 0 := le_refl 0
  have h4 : 1 ≤ 0 := h1 h2 h3
  linarith

-- Lemas usados
-- ============

-- variable (a c : ℝ)
-- #check (le_refl a : a ≤ a)
-- #check (monotone_const : Monotone fun _ : ℝ ↦ c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_de_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
