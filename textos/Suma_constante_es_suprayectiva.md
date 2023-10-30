---
Título: La función (x ↦ x + c) es suprayectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que la función \\(x ↦ x + c\\) es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {c : ℝ}
open Function

example : Surjective (fun x ↦ x + c) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Tenemos que demostrar que
\\[ (∀ x ∈ ℝ)(∃ y ∈ ℝ)[y+c = x] \\]
Sea \\(x ∈ ℝ\\). Entonces, \\(y = x-c ∈ ℝ\\) y
\\begin{align}
   y + c &= (x - c) + c \\\\
         &= x
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {c : ℝ}

open Function

-- 1ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  dsimp
  -- ⊢ (x - c) + c = x
  exact sub_add_cancel x c

-- 2ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  change (x - c) + c = x
  -- ⊢ (x - c) + c = x
  exact sub_add_cancel x c

-- 3ª demostración
example : Surjective (fun x ↦ x + c) :=
by
  intro x
  -- x : ℝ
  -- ⊢ ∃ a, (fun x => x + c) a = x
  use x - c
  -- ⊢ (fun x => x + c) (x - c) = x
  exact sub_add_cancel x c

-- 4ª demostración
example : Surjective (fun x ↦ x + c) :=
fun x ↦ ⟨x - c, sub_add_cancel x c⟩

-- 5ª demostración
example : Surjective (fun x ↦ x + c) :=
fun x ↦ ⟨x - c, by ring⟩

-- 6ª demostración
example : Surjective (fun x ↦ x + c) :=
add_right_surjective c

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (sub_add_cancel a b : (a - b) + b = a)
-- #check (add_right_surjective c : Surjective (fun x ↦ x + c))
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_constante_es_suprayectiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 31.</li>
</ul>
