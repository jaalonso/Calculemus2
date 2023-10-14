---
Título: Si f es par y g es impar, entonces (f ∘ g) es par
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(f\\) es par y \\(g\\) es impar, entonces \\(f ∘ g\\) es par.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- (esPar f) expresa que f es par.
def esPar (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

-- (esImpar f) expresa que f es impar.
def esImpar  (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = - f (-x)

example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Supongamos que \\(f\\) es una función par y \\(g\\) lo es impar. Tenemos que demostrar que \\(f ∘ g\\) es par; es decir, que
\\[ (∀ x ∈ ℝ) (f ∘ g)(x) = (f ∘ g)(-x) \\]
Sea \\(x ∈ ℝ\\). Entonces,
\\begin{align}
   (f ∘ g)(x) &= f(g(x))      \\\\
              &= f(-g(-x))    &&\\text{[porque \\(g\\) es impar]} \\\\
              &= f(g(-x))     &&\\text{[porque \\(f\\) es par]} \\\\
              &= (f ∘ g)(-x)
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- (esPar f) expresa que f es par.
def esPar (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

-- (esImpar f) expresa que f es impar.
def esImpar  (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = - f (-x)

-- 1ª demostración
example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
    _  = f (-g (-x))  := congr_arg f (h2 x)
    _  = f (g (-x))   := (h1 (g (-x))).symm
    _  = (f ∘ g) (-x) := rfl

-- 2ª demostración
example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
     _ = f (-g (-x))  := by rw [h2]
     _ = f (g (-x))   := by rw [← h1]
     _ = (f ∘ g) (-x) := rfl

-- 3ª demostración
example
  (h1 : esPar f)
  (h2 : esImpar g)
  : esPar (f ∘ g) :=
by
  intro x
  calc (f ∘ g) x
       = f (g x)      := rfl
     _ = f (g (-x))   := by rw [h2, ← h1]
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Composicion_de_par_e_impar.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 26.</li>
</ul>
