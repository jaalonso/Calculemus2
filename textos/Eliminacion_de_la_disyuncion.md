---
Título: En ℝ, si x < |y|, entonces x < y ó x < -y.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), si \\(x < |y|\\), entonces \\(x < y\\) ó \\(x < -y\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

example : x < |y| → x < y ∨ x < -y :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se demostrará por casos según \\(y ≥ 0\\).

Primer caso: Supongamos que \\(y ≥ 0\\). Entonces, \\(|y| = y\\) y, por tanto, \\(x < y\\).

Segundo caso: Supongamos que \\(y < 0\\). Entonces, \\(|y| = -y\\) y, por tanto, \\(x < -y\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example : x < |y| → x < y ∨ x < -y :=
by
  intro h1
  -- h1 : x < |y|
  -- ⊢ x < y ∨ x < -y
  cases' le_or_gt 0 y with h2 h3
  . -- h2 : 0 ≤ y
    left
    -- ⊢ x < y
    rwa [abs_of_nonneg h2] at h1
  . -- h3 : 0 > y
    right
    -- ⊢ x < -y
    rwa [abs_of_neg h3] at h1

-- 2ª demostración
-- ===============

example : x < |y| → x < y ∨ x < -y :=
lt_abs.mp

-- Lemas usados
-- ============

-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (abs_of_nonneg : 0 ≤ x → abs x = x)
-- #check (abs_of_neg : x < 0 → abs x = -x)
-- #check (lt_abs : x < |y| ↔ x < y ∨ x < -y)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Eliminacion_de_la_disyuncion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
