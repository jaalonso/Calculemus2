---
Título: En ℝ, a < b → ¬(b < a)
Autor:  José A. Alonso
---

Demostrar con Lean4 que en \\(ℝ\\), \\(a < b → ¬(b < a)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example
  (h : a < b)
  : ¬ b < a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por hipótesis \\(a < b\\) y tenemos que demostrar que \\(¬(b < a)\\). Supongamos que \\(b < a\\). Entonces, por la propiedad transiva \\(a < a\\) que es una contradicción con la propiedad irreflexiva.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- 1ª demostración
example
  (h : a < b)
  : ¬ b < a :=
by
  intro h1
  -- h1 : b < a
  -- ⊢ False
  have : a < a := lt_trans h h1
  apply lt_irrefl a this

-- 2ª demostración
example
  (h : a < b)
  : ¬ b < a :=
by
  intro h1
  -- h1 : b < a
  -- ⊢ False
  exact lt_irrefl a (lt_trans h h1)

-- 3ª demostración
example
  (h : a < b)
  : ¬ b < a :=
fun h1 ↦ lt_irrefl a (lt_trans h h1)

-- 4ª demostración
example
  (h : a < b)
  : ¬ b < a :=
lt_asymm h

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (lt_asymm : a < b → ¬b < a)
-- #check (lt_irrefl a : ¬a < a)
-- #check (lt_trans : a < b → b < c → a < c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Asimetria_de_menor.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 32.</li>
</ul>
