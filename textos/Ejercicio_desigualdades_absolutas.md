---
Título: En ℝ, |ab| ≤ (a²+b²)/2
Autor:  José A. Alonso
---

Sean \(a\) y \(b\) números reales. Demostrar con Lean4 que
\[|ab| \leq \frac{a^2 + b^2}{2}\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example : |a * b| \leq (a ^ 2 + b ^ 2) / 2 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Para demostrar
\[|ab| \leq \frac{a^2 + b^2}{2}\]
basta demostrar estas dos desigualdades
\begin{align}
   ab    &\leq \frac{a^2 + b^2}{2} \tag{1} \\
   -(ab) &\leq \frac{a^2 + b^2}{2} \tag{2}
\end{align}

Para demostrar (1) basta demostrar que
\[2ab \leq a^2 + b^2\]
que se prueba como sigue. En primer lugar, como los cuadrados son no negativos, se tiene
\[(a - b)^2 \geq 0\]
Desarrollando el cuandrado,
\[a^2 - 2ab + b^2 \geq 0\]
Sumando \(2ab\),
\[a^2 + b^2 \geq 2ab\]

Para demostrar (2) basta demostrar que
\[-2ab \leq a^2 + b^2\]
que se prueba como sigue. En primer lugar, como los cuadrados son no
negativos, se tiene
\[(a + b)^2 \geq 0\]
Desarrollando el cuandrado,
\[a^2 + 2ab + b^2 \geq 0\]
Restando \(2ab\),
\[a^2 + b^2 \geq -2ab\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- Lemas auxiliares
-- ================

lemma aux1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2
      = (a - b) ^ 2            := by ring
    _ ≥ 0                      := pow_two_nonneg (a - b)
  linarith only [h]

lemma aux2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2
      = (a + b) ^ 2            := by ring
    _ ≥ 0                      := pow_two_nonneg (a + b)
  linarith only [h]

-- 1ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { have h1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := aux1 a b
    show a * b ≤ (a ^ 2 + b ^ 2) / 2
    exact (le_div_iff h).mpr h1 }
  { have h2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := aux2 a b
    show -(a * b) ≤ (a ^ 2 + b ^ 2) / 2
    exact (le_div_iff h).mpr h2 }

-- 2ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { exact (le_div_iff h).mpr (aux1 a b) }
  { exact (le_div_iff h).mpr (aux2 a b) }

-- 3ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { rw [le_div_iff h]
    apply aux1 }
  { rw [le_div_iff h]
    apply aux2 }
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_desigualdades_absolutas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 16.</li>
</ul>
