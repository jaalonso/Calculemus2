---
Título: La suma de dos funciones monótonas es monótona
Autor:  José A. Alonso
---

Demostrar con Lean4 que la suma de dos funciones monótonas es monótona.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el siguiente lema:
\\[ \\{a ≤ b, c ≤ d\\} ⊢ a + c ≤ b + d \\tag{L1} \\]

Supongamos que \\(f\\) y \\(g\\) son monótonas y teneno que demostrar que \\(f+g\\) también lo es; que
\\[ (∀ a,\\ b \\in ℝ) [a ≤ b → (f + g)(a) ≤ (f + g)(b)] \\]
Sean \\(a, b ∈ ℝ\\) tales que
\\[ a ≤ b \\tag{1} \\]
Entonces, por ser \\(f\\) y \\(g\\) monótonas se tiene
\\begin{align}
   f(a) &≤ f(b) \\tag{2} \\\\
   g(a) &≤ g(b) \\tag{3}
\\end{align}
Entonces,
\\begin{align}
   (f + g)(a) &= f(a) + g(a)    \\\\
              &≤ f(b) + g(b)    &&\\text{[por L1, (2) y (3)]} \\\\
              &= (f + g)(b)
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- 1ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b
  { intros a b hab
    have h2 : f a ≤ f b := mf hab
    have h3 : g a ≤ g b := mg hab
    calc (f + g) a
         = f a + g a := rfl
       _ ≤ f b + g b := add_le_add h2 h3
       _ = (f + g) b := rfl }
  show Monotone (f + g)
  exact h1

-- 2ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b
  { intros a b hab
    calc (f + g) a
         = f a + g a := rfl
       _ ≤ f b + g b := add_le_add (mf hab) (mg hab)
       _ = (f + g) b := rfl }
  show Monotone (f + g)
  exact h1

-- 3ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b
  { intros a b hab
    show (f + g) a ≤ (f + g) b
    exact add_le_add (mf hab) (mg hab) }
  show Monotone (f + g)
  exact h1

-- 4ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  -- a b : ℝ
  -- hab : a ≤ b
  intros a b hab
  apply add_le_add
  . -- f a ≤ f b
    apply mf hab
  . --  g a ≤ g b
    apply mg hab

-- 5ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
λ _ _ hab ↦ add_le_add (mf hab) (mg hab)

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_de_funciones_monotonas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 26.</li>
</ul>
