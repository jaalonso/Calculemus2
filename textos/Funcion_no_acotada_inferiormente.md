---
Título: Si para cada a existe un x tal que f(x) < a, entonces f no tiene cota inferior.
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(f\\) es una función de \\(ℝ\\) en \\(ℝ\\) tal que para cada \\(a\\) existe un \\(x\\) tal que \\(f(x) < a\\), entonces \\(f\\) no tiene cota inferior.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def acotadaInf (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaInferior f a

variable (f : ℝ → ℝ)

example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ acotadaInf f :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Supongamos que \\(f\\) tiene cota inferior. Sea \\(b\\) una de dichas cotas inferiores. Por la hipótesis, existe un \\(x\\) tal que \\(f(x) < b\\). Además, como \\(b\\) es una cota inferior de \\(f\\), \\(b ≤ f(x)\\) que contradice la desigualdad anterior.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def acotadaInf (f : ℝ → ℝ) : Prop :=
  ∃ a, CotaInferior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ acotadaInf f :=
by
  intros hf
  -- hf : acotadaInf f
  -- ⊢ False
  cases' hf with b hb
  -- b : ℝ
  -- hb : CotaInferior f b
  cases' h b with x hx
  -- x : ℝ
  -- hx : f x < b
  have : b ≤ f x := hb x
  linarith

-- 2ª demostración
example
  (h : ∀ a, ∃ x, f x < a)
  : ¬ acotadaInf f :=
by
  intros hf
  -- hf : acotadaInf f
  -- ⊢ False
  rcases hf with ⟨b, hb : CotaInferior f b⟩
  rcases h b with ⟨x, hx : f x < b⟩
  have : b ≤ f x := hb x
  linarith
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Funcion_no_acotada_inferiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
