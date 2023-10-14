---
Título: Si c es no negativo y f es monótona, entonces cf es monótona.
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(c\\) es no negativo y \\(f\\) es monótona, entonces \\(cf\\) es monótona.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f : ℝ → ℝ)
variable {c : ℝ}

example
  (mf : Monotone f)
  (nnc : 0 ≤ c)
  : Monotone (fun x ↦ c * f x) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el Lema
\\[ \\{b ≤ c, 0 ≤ a\\} ⊢ ab ≤ ac \\tag{L1} \\]

Tenemos que demostrar que
\\[ (∀ a, b ∈ ℝ) [a ≤ b → (cf)(a) ≤ (cf)(b)] \\]
Sean \\(a, b ∈ ℝ\\) tales que \\(a ≤ b\\). Puesto que \\(f\\) es monótona, se tiene
\\[ f(a) ≤ f(b) \\]
y, junto con la hipótesis de que \\(c\\) es no negativo, usando el lema L1, se tiene que
\\[ cf(a) ≤ cf(b) \\]
que es lo que había que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f : ℝ → ℝ)
variable {c : ℝ}

-- 1ª demostración
example
  (mf : Monotone f)
  (nnc : 0 ≤ c)
  : Monotone (fun x ↦ c * f x) :=
by
  have h1 : ∀ a b, a ≤ b → (fun x ↦ c * f x) a ≤ (fun x ↦ c * f x) b
  { intros a b hab
    have h2 : f a ≤ f b := mf hab
    show (fun x ↦ c * f x) a ≤ (fun x ↦ c * f x) b
    exact mul_le_mul_of_nonneg_left h2 nnc }
  show Monotone (fun x ↦ c * f x)
  exact h1

-- 2ª demostración
example
  (mf : Monotone f)
  (nnc : 0 ≤ c)
  : Monotone (fun x ↦ c * f x) :=
by
  -- a b : ℝ
  -- hab : a ≤ b
  intros a b hab
  -- (fun x => c * f x) a ≤ (fun x => c * f x) b
  apply mul_le_mul_of_nonneg_left
  . -- f a ≤ f b
    apply mf hab
  . -- 0 ≤ c
    apply nnc

-- 3ª demostración
example (mf : Monotone f) (nnc : 0 ≤ c) :
  Monotone (fun x ↦ c * f x) :=
λ _ _ hab ↦ mul_le_mul_of_nonneg_left (mf hab) nnc

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_un_positivo_por_una_funcion_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 26.</li>
</ul>
