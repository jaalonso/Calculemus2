--
Título: Si R es un anillo y a, b, c ∈ R tales que a+b=a+c, entonces b=c
Autor:  José A. Alonso
---

Demostrar con Lean4 que si R es un anillo y a, b, c ∈ R tales que
<pre lang="text">
   a + b = a + c
</pre>
entonces
<pre lang="text">
   b = c
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

example
  (h : a + b = a + c)
  : b = c :=
sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
b &= 0 + b           &&\text{[por suma con cero]} \\
  &= (-a + a) + b    &&\text{[por suma con opuesto]} \\
  &= -a + (a + b)    &&\text{[por asociativa]} \\
  &= -a + (a + c)    &&\text{[por hipótesis]} \\
  &= (-a + a) + c    &&\text{[por asociativa]} \\
  &= 0 + c           &&\text{[por suma con opuesto]} \\
  &= c               &&\text{[por suma con cero]}
\end{align}

<b>2ª demostración en LN</b>

Por la siguiente cadena de implicaciones
\begin{align}
a + b = a + c
&\Longrightarrow -a + (a + b) = -a + (a + c)     &&\text{[sumando -a]} \\
&\Longrightarrow  (-a + a) + b = (-a + a) + c    &&\text{[por la asociativa]} \\
&\Longrightarrow  0 + b = 0 + b                  &&\text{[suma con opuesto]} \\
&\Longrightarrow  b = c                          &&\text{[suma con cero]}
\end{align}

<b>3ª demostración en LN</b>

Por la siguiente cadena de igualdades
\begin{align}
b &= -a + (a + b)   \\
  &= -a + (a + c)   &&\text{[por la hipótesis]} \\
  &= c
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a b c : R}

-- 1ª demostración
example
  (h : a + b = a + c)
  : b = c :=
calc
  b = 0 + b        := by rw [zero_add]
  _ = (-a + a) + b := by rw [add_left_neg]
  _ = -a + (a + b) := by rw [add_assoc]
  _ = -a + (a + c) := by rw [h]
  _ = (-a + a) + c := by rw [←add_assoc]
  _ = 0 + c        := by rw [add_left_neg]
  _ = c            := by rw [zero_add]

-- 2ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  have h1 : -a + (a + b) = -a + (a + c) :=
    congrArg (HAdd.hAdd (-a)) h
  clear h
  rw [← add_assoc] at h1
  rw [add_left_neg] at h1
  rw [zero_add] at h1
  rw [← add_assoc] at h1
  rw [add_left_neg] at h1
  rw [zero_add] at h1
  exact h1

-- 3ª demostración
example
  (h : a + b = a + c)
  : b = c :=
calc
  b = -a + (a + b) := by rw [neg_add_cancel_left a b]
  _ = -a + (a + c) := by rw [h]
  _ = c            := by rw [neg_add_cancel_left]

-- 4ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b]
  rw [h]
  rw [neg_add_cancel_left]

-- 5ª demostración
example
  (h : a + b = a + c)
  : b = c :=
by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

-- 6ª demostración
example
  (h : a + b = a + c)
  : b = c :=
add_left_cancel h
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cancelativa_izquierda.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 11.</li>
</ul>
