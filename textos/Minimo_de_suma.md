---
Título: En ℝ, min(a,b)+c = min(a+c,b+c)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(a\), \(b\) y \(c\) números reales, entonces
\[\min(a,b)+c = \min(a+c,b+c)\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {a b c : ℝ}

example :
  min a b + c = min (a + c) (b + c) :=
by sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Aplicando la propiedad antisimétrica a las siguientes desigualdades
\begin{align}
   \min(a, b) + c \leq \min(a + c, b + c) \tag{1} \\
   \min(a + c, b + c) \leq \min(a, b) + c \tag{2}
\end{align}

Para demostrar (1) basta demostrar que se verifican las siguientes desigualdades
\begin{align}
   \min(a, b) + c &\leq a + c \tag{1a} \\
   \min(a, b) + c &\leq b + c \tag{1b}
\end{align}
que se tienen porque se verifican las siguientes desigualdades
\begin{align}
   \min(a, b) &\leq a \\
   \min(a, b) &\leq b
\end{align}

Para demostrar (2) basta demostrar que se verifica
\[ \min(a + c, b + c) - c \leq \min(a, b) \]
que se demuestra usando (1); en efecto,
\begin{align}
   \min(a + c, b + c) - c &\leq \min(a + c - c, b + c - c)    &&\text{[por (1)]}\\
                          &= \min(a, b)
\end{align}

<b>2ª demostración en LN</b>

Por casos según \(a \leq b\).

1º caso: Supongamos que \(a \leq b\). Entonces,
\begin{align}
   \min(a, b) + c &= a + c              \\
                  &= \min(a + c, b + c)
\end{align}

2º caso: Supongamos que \(a \nleq b\). Entonces,
\begin{align}
   \min(a, b) + c &= b + c                \\
                  &= \min(a + c, b + c)
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {a b c : ℝ}

-- En las demostraciones se usarán los siguientes lemas auxiliares
--    aux1 : min a b + c ≤ min (a + c) (b + c)
--    aux2 : min (a + c) (b + c) ≤ min a b + c
-- cuyas demostraciones se exponen a continuación.

-- 1ª demostración de aux1
lemma aux1 :
  min a b + c ≤ min (a + c) (b + c) :=
by
  have h1 : min a b ≤ a :=
    min_le_left a b
  have h2 : min a b + c ≤ a + c :=
    add_le_add_right h1 c
  have h3 : min a b  ≤ b :=
    min_le_right a b
  have h4 : min a b + c ≤ b + c :=
    add_le_add_right h3 c
  show min a b + c ≤ min (a + c) (b + c)
  exact le_min h2 h4

-- 2ª demostración de aux1
example :
  min a b + c ≤ min (a + c) (b + c) :=
by
  apply le_min
  { apply add_le_add_right
    exact min_le_left a b }
  { apply add_le_add_right
    exact min_le_right a b }

-- 3ª demostración de aux1
example :
  min a b + c ≤ min (a + c) (b + c) :=
le_min (add_le_add_right (min_le_left a b) c)
       (add_le_add_right (min_le_right a b) c)

-- 1ª demostración de aux2
lemma aux2 :
  min (a + c) (b + c) ≤ min a b + c :=
by
  have h1 : min (a + c) (b + c) + -c ≤ min a b
  { calc min (a + c) (b + c) + -c
         ≤ min (a + c + -c) (b + c + -c) := aux1
       _ = min a b                       := by ring_nf }
  show min (a + c) (b + c) ≤ min a b + c
  exact add_neg_le_iff_le_add.mp h1

-- 1ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  have h1 : min a b + c ≤ min (a + c) (b + c) := aux1
  have h2 : min (a + c) (b + c) ≤ min a b + c := aux2
  show min a b + c = min (a + c) (b + c)
  exact le_antisymm h1 h2

-- 2ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  apply le_antisymm
  { show min a b + c ≤ min (a + c) (b + c)
    exact aux1 }
  { show min (a + c) (b + c) ≤ min a b + c
    exact aux2 }

-- 3ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  apply le_antisymm
  { exact aux1 }
  { exact aux2 }

-- 4ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
le_antisymm aux1 aux2

-- 5ª demostración del ejercicio
example : min a b + c = min (a + c) (b + c) :=
by
  by_cases h : a ≤ b
  { have h1 : a + c ≤ b + c := add_le_add_right h c
    calc min a b + c = a + c               := by simp [min_eq_left h]
                   _ = min (a + c) (b + c) := by simp [min_eq_left h1]}
  { have h2: b ≤ a := le_of_not_le h
    have h3 : b + c ≤ a + c := add_le_add_right h2 c
    calc min a b + c = b + c               := by simp [min_eq_right h2]
                   _ = min (a + c) (b + c) := by simp [min_eq_right h3]}

-- 6ª demostración del ejercicio
example : min a b + c = min (a + c) (b + c) :=
(min_add_add_right a b c).symm
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Minimo_de_suma.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 18.</li>
</ul>
