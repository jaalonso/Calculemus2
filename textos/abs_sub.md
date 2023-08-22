---
Título: En ℝ, |a| - |b| ≤ |a - b|
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\) y \(b\) números reales, entonces
\[|a| - |b| \leq |a - b|\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

example : |a| - |b| ≤ |a - b| :=
by sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Por la siguiente cadena de desigualdades
\begin{align}
   |a| - |b| &= |a - b + b| - |b| \\
             &\leq (|a - b| + |b|) - |b|   &&\text{[por la desigualdad triangular]}\\
             &= |a - b|
\end{align}

<b>2ª demostración en LN</b>

Por la desigualdad triangular
\[   |a - b + b| \leq |a - b| + |b| \]
simplificando en la izquierda
\[   |a| \leq |a - b| + |b| \]
y, pasando \(|b|\) a la izquierda
\[   |a| - |b| ≤ |a - b| \]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- 1ª demostración (basada en la 1ª en LN)
example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b| :=
          congrArg (fun x => |x| - |b|) (sub_add_cancel a b).symm
   _ ≤ (|a - b| + |b|) - |b| :=
           sub_le_sub_right (abs_add (a - b) b) (|b|)
   _ = |a - b| :=
          add_sub_cancel (|a - b|) (|b|)

-- 2ª demostración (basada en la 1ª en LN)
example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b| := by
          rw [sub_add_cancel]
   _ ≤ (|a - b| + |b|) - |b| := by
          apply sub_le_sub_right
          apply abs_add
   _ = |a - b| := by
          rw [add_sub_cancel]

-- 3ª demostración (basada en la 2ª en LN)
example : |a| - |b| ≤ |a - b| :=
by
  have h1 : |a - b + b| ≤ |a - b| + |b| := abs_add (a - b) b
  rw [sub_add_cancel] at h1
  exact abs_sub_abs_le_abs_sub a b

-- 4ª demostración
example : |a| - |b| ≤ |a - b| :=
abs_sub_abs_le_abs_sub a b
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/abs_sub.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 18.</li>
</ul>
