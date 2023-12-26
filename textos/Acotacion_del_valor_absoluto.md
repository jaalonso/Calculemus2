---
Título: Si |x + 3| < 5, entonces -8 < x < 2.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(|x + 3| < 5\\), entonces \\(-8 < x < 2\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Supongamos que
\\[ |x + 3| < 5 \\]
entonces
\\[ -5 < x + 3 < 5 \\]
por tanto
\\[ -8 < x < 2 \\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  -- ⊢ -5 < x + 3 ∧ x + 3 < 5 → -8 < x ∧ x < 2
  intro h
  -- h : -5 < x + 3 ∧ x + 3 < 5
  -- ⊢ -8 < x ∧ x < 2
  constructor
  . -- ⊢ -8 < x
    linarith
  . -- x < 2
    linarith

-- 2ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  intro h
  constructor <;> linarith

-- Comentario: La composición (constructor <;> linarith) aplica constructor y a
-- continuación le aplica linarith a cada subojetivo.

-- 3ª demostración
-- ===============

example
  : |x + 3| < 5 → -8 < x ∧ x < 2 :=
by
  rw [abs_lt]
  exact fun _ ↦ ⟨by linarith, by linarith⟩

-- Lemas usados
-- ============

-- #check (abs_lt: |x| < y ↔ -y < x ∧ x < y)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Acotacion_del_valor_absoluto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 37.</li>
</ul>
