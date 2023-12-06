---
Título: Si 0 < 0, entonces a > 37 para cualquier número a.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(0 < 0\\), entonces \\(a > 37\\) para cualquier número \\(a\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable (a : ℕ)

example
  (h : 0 < 0)
  : a > 37 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Basta demostrar una contradicción, ya que de una contradicción se sigue cualquier cosa.

La hipótesis es una contradicción con la propiedad irreflexiva de la relación \\(<\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

variable (a : ℕ)

-- 1ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  exfalso
  -- ⊢ False
  show False
  exact lt_irrefl 0 h

-- 2ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  exfalso
  -- ⊢ False
  apply lt_irrefl 0 h

-- 3ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
absurd h (lt_irrefl 0)

-- 4ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by
  have : ¬ 0 < 0 :=  lt_irrefl 0
  contradiction

-- 5ª demostración
-- ===============

example
  (h : 0 < 0)
  : a > 37 :=
by linarith

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- #check (lt_irrefl a : ¬a < a)
-- #check (absurd : p → ¬p → q)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Principio_de_explosion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 34.</li>
</ul>
