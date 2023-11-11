---
Título: Si c ≠ 0, entonces la función (x ↦ cx + d) es suprayectiva
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(c ≠ 0\\), entonces la función \\(x ↦ cx + d\\) es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {c d : ℝ}
open Function

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Hay que demostrar que
\\[ (∀x ∈ ℝ)(∃y ∈ ℝ)[cy+d = x] \\]
Para \\(x ∈ ℝ\\), sea \\(y = \\frac{x-d}{c}\\). Entonces,
\\begin{align}
   cy &= c\\left(\\frac{x-d}{c}\\right)+d \\\\
      &= (x-d)+d      \\\\
      &= x
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {c d : ℝ}
open Function

-- 1ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  dsimp
  -- ⊢ c * ((x - d) / c) + d = x
  show c * ((x - d) / c) + d = x
  calc c * ((x - d) / c) + d
         = (x - d) + d := congrArg (. + d) (mul_div_cancel' (x - d) h)
       _ = x           := sub_add_cancel x d

-- 2ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  dsimp
  -- ⊢ c * ((x - d) / c) + d = x
  simp [mul_div_cancel', h]

-- 3ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x + d) a = x
  use ((x - d) / c)
  -- ⊢ (fun x => c * x + d) ((x - d) / c) = x
  simp [mul_div_cancel', h]

-- 4ª demostración
-- ===============

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x + d) :=
fun x ↦ ⟨(x - d) / c, by simp [mul_div_cancel', h]⟩

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_div_cancel' a : b ≠ 0 → b * (a / b) = a)
-- #check (sub_add_cancel a b : a - b + b = a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_por_no_nula_y_suma_es_suprayectiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
