---
Título: El producto de funciones no negativas es no negativo
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(f\\) y \\(g\\) son funciones no negativas de \\(ℝ\\) en \\(ℝ\\), entonces su producto es no negativo.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)

example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el siguiente lema
\\[ \\{0 ≤ a, 0 ≤ b\\} \\vdash 0 ≤ ab \\tag{L1} \\]

Hay que demostrar que
\\[ (∀ x ∈ ℝ) [0 ≤ f(x)g(x)] \\tag{1} \\]
Para ello, sea \\(x ∈ R\\). Puesto que \\(f\\) es no negatica, se tiene que
\\[ 0 ≤ f(x) \\tag{2} \\]
y, puesto que \\(g\\) es no negativa, se tiene que
\\[ 0 ≤ g(x) \\tag{3} \\]
De (2) y (3), por L1, se tiene que
\\[ 0 ≤ f(x)g(x) \\]
que es lo que había que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)

-- 1ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x
  { intro x
    have h2: 0 ≤ f x := nnf x
    have h3: 0 ≤ g x := nng x
    show 0 ≤ f x * g x
    exact mul_nonneg h2 h3 }
  show CotaInferior (f * g) 0
  exact h1

-- 2ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  have h1 : ∀x, 0 ≤ f x * g x
  { intro x
    show 0 ≤ f x * g x
    exact mul_nonneg (nnf x) (nng x) }
  show CotaInferior (f * g) 0
  exact h1

-- 3ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
by
  intro x
  dsimp
  apply mul_nonneg
  . apply nnf
  . apply nng

-- 4ª demostración
example
  (nnf : CotaInferior f 0)
  (nng : CotaInferior g 0)
  : CotaInferior (f * g) 0 :=
λ x ↦ mul_nonneg (nnf x) (nng x)

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_funciones_no_negativas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 25.</li>
</ul>
