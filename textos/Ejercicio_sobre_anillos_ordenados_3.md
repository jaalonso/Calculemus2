---
Título: En los anillos ordenados, {a ≤ b, 0 ≤ c} ⊢ ac ≤ bc
Autor:  José A. Alonso
---

Demostrar con Lean4 que, en los anillos ordenados,
\[ \{a ≤ b, 0 ≤ c\} ⊢ ac ≤ bc \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usarán los siguientes lemas:
\begin{align}
   &0 ≤ a - b ↔ b ≤ a           \tag{L1} \\
   &0 ≤ a → 0 ≤ b → 0 ≤ ab      \tag{L2} \\
   &(a - b)c = ac - bc          \tag{L3}
\end{align}

Supongamos que
\begin{align}
   a &≤ b \tag{1} \\
   0 &≤ c
\end{align}
De (1), por L1, se tiene
\[   0 ≤ b - a \]
y con (2), por L2, se tiene
\[   0 ≤ (b - a)c \]
que, por L3, da
\[   0 ≤ bc - ac \]
y, aplicándole L1, se tiene
\[   ac ≤ bc \]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a :=
    sub_nonneg.mpr h1
  have h4 : 0 ≤ b * c - a * c := calc
    0 ≤ (b - a) * c   := mul_nonneg h3 h2
    _ = b * c - a * c := sub_mul b a c
  show a * c ≤ b * c
  exact sub_nonneg.mp h4

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  have h3 : 0 ≤ b - a := sub_nonneg.mpr h1
  have h4 : 0 ≤ (b - a) * c := mul_nonneg h3 h2
  -- h4 : 0 ≤ b * c - a * c
  rw [sub_mul] at h4
  -- a * c ≤ b * c
  exact sub_nonneg.mp h4

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  -- 0 ≤ b * c - a * c
  apply sub_nonneg.mp
  -- 0 ≤ (b - a) * c
  rw [← sub_mul]
  apply mul_nonneg
  . -- 0 ≤ b - a
    exact sub_nonneg.mpr h1
  . -- 0 ≤ c
    exact h2

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
by
  apply sub_nonneg.mp
  rw [← sub_mul]
  apply mul_nonneg (sub_nonneg.mpr h1) h2

-- 5ª demostración
example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
-- by apply?
mul_le_mul_of_nonneg_right h1 h2

-- Lemas usados
-- ============

-- #check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
-- #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- #check (sub_mul a b c : (a - b) * c = a * c - b * c)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_sobre_anillos_ordenados_3.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 22.</li>
</ul>
