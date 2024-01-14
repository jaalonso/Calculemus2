---
Título: En ℝ, si x ≠ 0 entonces x < 0 ó x > 0.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en ℝ, si \\(x ≠ 0\\) entonces \\(x < 0\\) ó \\(x > 0\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usando el siguiente lema
\\[ (∀ x y ∈ ℝ)[x < y ∨ x = y ∨ y < x] \\]
se demuestra distinguiendo tres casos.

Caso 1: Supongamos que \\(x < 0\\). Entonces, se verifica la disyunción ya
que se verifica su primera parte.

Caso 2: Supongamos que \\(x = 0\\). Entonces, se tiene una contradicción
con la hipótesis.

Caso 3: Supongamos que \\(x > 0\\). Entonces, se verifica la disyunción ya
que se verifica su segunda parte.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x : ℝ}

-- 1ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
by
  rcases lt_trichotomy x 0 with hx1 | hx2 | hx3
  . -- hx1 : x < 0
    left
    -- ⊢ x < 0
    exact hx1
  . -- hx2 : x = 0
    contradiction
  . -- hx3 : 0 < x
    right
    -- ⊢ x > 0
    exact hx3

-- 2ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
Ne.lt_or_lt h

-- 3ª demostración
-- ===============

example
  (h : x ≠ 0)
  : x < 0 ∨ x > 0 :=
by aesop

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (lt_trichotomy x y : x < y ∨ x = y ∨ y < x)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Eliminacion_de_la_disyuncion_con_rcases.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>
