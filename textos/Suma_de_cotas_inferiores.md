---
Título: La suma de una cota inferior de f y una cota inferior de g es una cota inferior de f+g
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(f\) y \(g\) son funciones de \(ℝ\) en \(ℝ\), entonces la suma de una cota inferior de \(f\) y una cota inferior de \(g\) es una cota inferior de \(f+g\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el siguiente lema
\[ a ≤ b → c ≤ d → a + c ≤ b + d \tag{L1} \]

Por la definición de cota inferior, hay que demostrar que
\[ (∀ x ∈ ℝ) [a + b ≤ f(x) + g(x)] \tag{1} \]
Para ello, sea \(x ∈ R\). Puesto que es \(a\) es una cota inferior de \(f\), se tiene que
\[ a ≤ f(x) \tag{2} \]
y, puesto que \(b\) es una cota inferior de \(g\), se tiene que
\[ b ≤ g(x) \tag{3} \]
De (2) y (3), por L1, se tiene que
\[ a + b ≤ f(x) + g(x) \]
que es lo que había que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x
  { intro x
    have h1a : a ≤ f x := hfa x
    have h1b : b ≤ g x := hgb x
    show a + b ≤ f x + g x
    exact add_le_add h1a h1b }
  show CotaInferior (f + g) (a + b)
  exact h1

-- 2ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  have h1 : ∀ x, a + b ≤ f x + g x
  { intro x
    show a + b ≤ f x + g x
    exact add_le_add (hfa x) (hgb x) }
  show CotaInferior (f + g) (a + b)
  exact h1

-- 3ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  . apply hfa
  . apply hgb

-- 4ª demostración
example
  (hfa : CotaInferior f a)
  (hgb : CotaInferior g b)
  : CotaInferior (f + g) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_de_cotas_inferiores.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 25.</li>
</ul>
