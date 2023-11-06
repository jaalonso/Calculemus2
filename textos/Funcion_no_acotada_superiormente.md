---
    Título: Si para cada a existe un x tal que f(x) > a, entonces f no tiene cota superior.
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(f\\) es una función de \\(ℝ\\) en \\(ℝ\\) tal que para cada \\(a\\) existe un \\(x\\) tal que \\(f(x) > a\\), entonces \\(f\\) no tiene cota superior.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

example
  (h : ∀ a, ∃ x, f x > a)
  : ¬ acotadaSup f :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Supongamos que \\(f\\) tiene cota superior. Sea \\(b\\) una de dichas cotas superiores. Por la hipótesis, existe un \\(x\\) tal que \\(f(x) > b\\). Además, como \\(b\\) es una cota superior de \\(f\\), \\(f(x) ≤ b\\) que contradice la desigualdad anterior.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ a, ∃ x, f x > a)
  : ¬ acotadaSup f :=
by
  intros hf
  -- hf : acotadaSup f
  -- ⊢ False
  cases' hf with b hb
  -- b : ℝ
  -- hb : CotaSuperior f b
  cases' h b with x hx
  -- x : ℝ
  -- hx : f x > b
  have : f x ≤ b := hb x
  linarith

-- 2ª demostración
example
  (h : ∀ a, ∃ x, f x > a)
  : ¬ acotadaSup f :=
by
  intros hf
  -- hf : acotadaSup f
  -- ⊢ False
  rcases hf with ⟨b, hb : CotaSuperior f b⟩
  rcases h b with ⟨x, hx : f x > b⟩
  have : f x ≤ b := hb x
  linarith
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Funcion_no_acotada_superiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
