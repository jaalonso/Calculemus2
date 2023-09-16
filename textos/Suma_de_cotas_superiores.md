---
Título: La suma de una cota superior de f y una cota superior de g es una cota superior de f+g
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(f\) y \(g\) son funciones de \(ℝ\) en \(ℝ\), entonces la suma de una cota superior de \(f\) y una cota superior de \(g\) es una cota superior de \(f+g\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el siguiente lema
\[ a ≤ b → c ≤ d → a + c ≤ b + d \tag{L1} \]

Por la definición de cota superior, hay que demostrar que
\[ (∀ x ∈ ℝ) [f(x) + g(x) ≤ a + b] \tag{1} \]
Para ello, sea \(x ∈ R\). Puesto que \(a\) es una cota superior de \(f\), se tiene que
\[ f(x) ≤ a \tag{2} \]
y, puesto que \(b\) es una cota superior de \(g\), se tiene que
\[ g(x) ≤ b \tag{3} \]
De (2) y (3), por L1, se tiene que
\[ f(x) + g(x) ≤ a + b \]
que es lo que había que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  have h1 : ∀ x, (f + g) x  ≤ a + b := by
  { intro x
    have h2 : f x ≤ a := hfa x
    have h3 : g x ≤ b := hgb x
    show (f + g) x ≤ a + b
    exact add_le_add h2 h3 }
  show CotaSuperior (f + g) (a + b)
  exact h1

-- 2ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  have h1 : ∀ x, (f + g) x ≤ a + b := by
  { intro x
    show (f + g) x ≤ a + b
    exact add_le_add (hfa x) (hgb x) }
  show CotaSuperior (f + g) (a + b)
  exact h1

-- 3ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  . apply hfa
  . apply hgb

-- 4ª demostración
-- ===============

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
λ x ↦ add_le_add (hfa x) (hgb x)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_de_cotas_superiores.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 25.</li>
</ul>
