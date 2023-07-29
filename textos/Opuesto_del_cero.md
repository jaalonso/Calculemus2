---
Título: Si R es un anillo, entonces -0 = 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo, entonces
<pre lang="text">
   -0 = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]

example : (-0 : R) = 0 :=
sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Por la suma con cero se tiene
\[0 + 0 = 0\]
Aplicándole la propiedad
\[\forall a b ∈ R, a + b = 0 \to -a = b\]
se obtiene
\[-0 = 0\]

<b>2ª demostración en LN</b>

Puesto que
\[\forall a b ∈ R, a + b = 0 \to -a = b\]
basta demostrar que
\[0 + 0 = 0\]
que es cierta por la suma con cero.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]

-- 1ª demostración (basada en la 1ª en LN)
example : (-0 : R) = 0 :=
by
  have h1 : (0 : R) + 0 = 0 := add_zero 0
  show (-0 : R) = 0
  exact neg_eq_of_add_eq_zero_left h1

-- 2ª demostración (basada en la 2ª en LN)
example : (-0 : R) = 0 :=
by
  apply neg_eq_of_add_eq_zero_left
  rw [add_zero]

-- 3ª demostración
example : (-0 : R) = 0 :=
  neg_zero

-- 4ª demostración
example : (-0 : R) = 0 :=
by simp
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Opuesto_del_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
