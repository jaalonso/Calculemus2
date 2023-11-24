---
Título: Si ¬(∀a)(∃x)[f(x) > a]​, entonces f está acotada superiormente.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(¬(∀a)(∃x)[f(x) > a]\\)​, entonces \\(f\\) está acotada superiormente.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Tenemos que demostrar que \\(f\\) es acotada superiormente; es decir, que
\\[ (∃a)(∀x)[f(x) ≤ a] \\]
que es exactamente la fórmula obtenida interiorizando la negación en la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  unfold acotadaSup
  -- ⊢ ∃ a, CotaSuperior f a
  unfold CotaSuperior
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 2ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  unfold acotadaSup CotaSuperior
  -- ⊢ ∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h

-- 3ª demostración
-- ===============

example
  (h : ¬∀ a, ∃ x, f x > a)
  : acotadaSup f :=
by
  push_neg at h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  exact h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CS_de_acotada_superiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 34.</li>
</ul>
