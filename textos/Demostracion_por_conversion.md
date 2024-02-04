---
Título: En ℝ, si 1 < a, entonces a < aa
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \\(ℝ\\), si \\(1 < a\\), entonces \\(a < aa\\)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {a : ℝ}

example
  (h : 1 < a)
  : a < a * a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se usarán los siguientes lemas
\\begin{align}
   &0 < 1                                      \\tag{L1} \\\\
   &(∀ a ∈ ℝ[1a = a]                           \\tag{L2} \\\\
   &(∀ a, b, c ∈ ℝ)[0 < a → (ba < ca ↔ b < c)] \\tag{L3}
\\end{align}

En primer lugar, tenemos que
\\[ 0 < a \\tag{1} \\]
ya que
\\begin{align}
   0 &< 1    &&\\text{[por L1]} \\\\
     &< a    &&\\text{[por la hipótesis]}
\\end{align}
Entonces,
\\begin{align}
   a &= 1a   &&\\text{[por L2]} \\\\
     &< aa   &&\\text{[por L3, (1) y la hipótesis]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {a : ℝ}

-- 1ª demostración
-- ===============

example
  (h : 1 < a)
  : a < a * a :=
by
  have h1 : 0 < a := calc
    0 < 1 := zero_lt_one
    _ < a := h
  show a < a * a
  calc a = 1 * a := (one_mul a).symm
       _ < a * a := (mul_lt_mul_right h1).mpr h

-- Comentarios: La táctica (convert e) genera nuevos subojetivos cuya
-- conclusiones son las diferencias entre el tipo de e y la conclusión.

-- 2ª demostración
-- ===============

example
  (h : 1 < a)
  : a < a * a :=
by
  convert (mul_lt_mul_right _).2 h
  . -- ⊢ a = 1 * a
    rw [one_mul]
  . -- ⊢ 0 < a
    exact lt_trans zero_lt_one h

-- Lemas usados
-- ============

-- variables (a b c : ℝ)
-- #check (mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c))
-- #check (one_mul a : 1 * a = a)
-- #check (lt_trans : a < b → b < c → a < c)
-- #check (zero_lt_one : 0 < 1)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/???Demostracion_por_conversion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 41.</li>
</ul>
