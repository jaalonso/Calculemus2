---
Título: Si R es un anillo y a, b, c ∈ R tales que a+b=c+b, entonces a=c
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a, b, c ∈ R tales que
<pre lang="text">
   a + b = c + b
</pre>
entonces
<pre lang="text">
   a = c
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

example
  (h : a + b = c + b)
  : a = c :=
sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN</b>

[mathjax]

<b>1ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
   a &= a + 0           &&\text{[por suma con cero]} \\
     &= a + (b + -b)    &&\text{[por suma con opuesto]} \\
     &= (a + b) + -b    &&\text{[por asociativa]} \\
     &= (c + b) + -b    &&\text{[por hipótesis]} \\
     &= c + (b + -b)    &&\text{[por asociativa]} \\
     &= c + 0           &&\text{[por suma con opuesto]} \\
     &= c               &&\text{[por suma con cero]}
\end{align}

<b>2ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
   a &= (a + b) + -b    \\
     &= (c + b) + -b    &&\text{[por hipótesis]} \\
     &= c
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

-- 1ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
calc
  a = a + 0        := by rw [add_zero]
  _ = a + (b + -b) := by rw [add_right_neg]
  _ = (a + b) + -b := by rw [add_assoc]
  _ = (c + b) + -b := by rw [h]
  _ = c + (b + -b) := by rw [← add_assoc]
  _ = c + 0        := by rw [← add_right_neg]
  _ = c            := by rw [add_zero]

-- 2ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
calc
  a = (a + b) + -b := (add_neg_cancel_right a b).symm
  _ = (c + b) + -b := by rw [h]
  _ = c            := add_neg_cancel_right c b

-- 3ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← add_neg_cancel_right a b]
  rw [h]
  rw [add_neg_cancel_right]

-- 4ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

-- 5ª demostración con Lean4
-- =========================

example
  (h : a + b = c + b)
  : a = c :=
add_right_cancel h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cancelativa_derecha.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
