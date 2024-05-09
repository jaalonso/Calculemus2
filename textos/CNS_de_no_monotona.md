---
Título: f: ℝ → ℝ no es monótona syss (∃x,y)[x ≤ y ∧ f(x) > f(y)]​.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que \\(f: ℝ → ℝ\\) no es monótona syss \\((∃x,y)[x ≤ y ∧ f(x) > f(y)]\\)​.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {f : ℝ → ℝ}

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Por la siguiente cadena de equivalencias:
\\begin{align}
   f \\text{ es no monótona } & ↔ ¬(∀ x y)[x ≤ y → f(x) ≤ f(y)] \\\\
                             & ↔ (∃ x y)[x ≤ y ∧ f(x) > f(y)]
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {f : ℝ → ℝ}

-- 1ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f y < f x  := by simp_all only [not_forall, not_le, exists_prop]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by rfl

-- 2ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
calc
  ¬Monotone f
    ↔ ¬∀ x y, x ≤ y → f x ≤ f y := by rw [Monotone]
  _ ↔ ∃ x y, x ≤ y ∧ f x > f y  := by aesop

-- 3ª demostración
-- ===============

example :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  push_neg
  -- ⊢ (Exists fun ⦃a⦄ => Exists fun ⦃b⦄ => a ≤ b ∧ f b < f a) ↔ ∃ x y, x ≤ y ∧ f x > f y
  rfl

-- 4ª demostración
-- ===============

lemma not_Monotone_iff :
  ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by
  rw [Monotone]
  -- ⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ x y, x ≤ y ∧ f x > f y
  aesop
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CNS-de_no_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 37.</li>
</ul>
