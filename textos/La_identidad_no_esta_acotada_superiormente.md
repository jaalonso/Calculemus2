---
Título: La función identidad no está acotada superiormente
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que la función identidad no está acotada superiormente.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import src.Funcion_no_acotada_superiormente

example : ¬ acotadaSup (fun x ↦ x) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usando el lema de ejercicio anterior (que afirma que si para cada \\(a\\), existe un \\(x\\) tal que \\(f(x) > a\\), entonces \\(f\\) no tiene cota superior) basta demostrar que
\\[ (∀a ∈ ℝ)(∃x ∈ ℝ) [x > a] \\]
Sea \\(a ∈ ℝ\\). Entonces \\(a + 1 > a\\) y, por tanto, \\((∃x ∈ ℝ) [x > a]\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import src.Funcion_no_acotada_superiormente

-- 1ª demostración
example : ¬ acotadaSup (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, x > a
  use a + 1
  -- ⊢ a + 1 > a
  linarith

-- 2ª demostración
example : ¬ acotadaSup (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, x > a
  exact ⟨a + 1, by linarith⟩

-- 3ª demostración
example : ¬ acotadaSup (fun x ↦ x) :=
by
  apply sinCotaSup
  -- ⊢ ∀ (a : ℝ), ∃ x, x > a
  exact fun a ↦ ⟨a + 1, by linarith⟩
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_identidad_no_esta_acotada_superiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
