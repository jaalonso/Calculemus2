---
Título: Si c ≠ 0, entonces la función (x ↦ cx) es suprayectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(c ≠ 0\\), entonces la función \\(x ↦ cx\\) es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {c : ℝ}
open Function

example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Hay que demostrar que
\\[ (∀ x ∈ ℝ)(∃ y ∈ ℝ)[cy = x] \\]
Sea \\(x ∈ ℝ\\). Entonces, \\(y = x/c ∈ R\\) y
\\begin{align}
   cy &= c(x/c) \\\\
      &= y
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {c : ℝ}
open Function

-- 1ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x) a = x
  use (x / c)
  -- ⊢ (fun x => c * x) (x / c) = x
  dsimp
  -- ⊢ c * (x / c) = x
  rw [mul_comm]
  -- ⊢ (x / c) * c = x
  exact div_mul_cancel x h

-- 2ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => c * x) a = x
  use (x / c)
  -- ⊢ (fun x => c * x) (x / c) = x
  exact mul_div_cancel' x h

-- 3ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
fun x ↦ ⟨x / c, mul_div_cancel' x h⟩

-- 4ª demostración
example
  (h : c ≠ 0)
  : Surjective (fun x ↦ c * x) :=
mul_left_surjective₀ h

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (div_mul_cancel a : b ≠ 0 → (a / b) * b = a)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_div_cancel' a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_left_surjective₀ : c ≠ 0 → Surjective (fun x ↦ c * x))
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_por_no_nula_es_suprayectiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 31.</li>
</ul>
