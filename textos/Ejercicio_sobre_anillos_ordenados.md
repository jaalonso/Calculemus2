---
Título: En los anillos ordenados, a ≤ b → 0 ≤ b - a
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los anillos ordenados se verifica que
\[ a ≤ b → 0 ≤ b - a \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

example : a ≤ b → 0 ≤ b - a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usarán los siguientes lemas:
\begin{align}
   &a - a = 0                        \tag{L1} \\
   &a ≤ b → ∀ (c : R), a - c ≤ b - c \tag{L2}
\end{align}

Supongamos que
\[ a ≤ b   \tag{(1)} \]
La demostración se tiene por la siguiente cadena de desigualdades:
\begin{align}
   0 &= a - a    &&\text{[por L1]} \\
     &≤ b - a    &&\text{[por (1) y L2]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
example : a ≤ b → 0 ≤ b - a :=
by
  intro h
  calc
    0 = a - a := (sub_self a).symm
    _ ≤ b - a := sub_le_sub_right h a

-- 2ª demostración
example : a ≤ b → 0 ≤ b - a :=
sub_nonneg.mpr

-- 3ª demostración
example : a ≤ b → 0 ≤ b - a :=
by simp

-- Lemas usados
-- ============

-- #check (sub_le_sub_right : a ≤ b → ∀ (c : R), a - c ≤ b - c)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
-- #check (sub_self a : a - a = 0)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_sobre_anillos_ordenados_1.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 22.</li>
</ul>
