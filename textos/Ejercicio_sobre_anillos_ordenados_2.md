---
Título: En los anillos ordenados, 0 ≤ b - a → a ≤ b
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los anillos ordenados
\[ 0 ≤ b - a → a ≤ b \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

example : 0 ≤ b - a → a ≤ b :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usarán los siguientes lemas:
\begin{align}
   &0 + a = a                     \tag{L1} \\
   &b ≤ c → (∀ a) [b + a ≤ c + a] \tag{L2} \\
   &a - b + b = -a                \tag{L3}
\end{align}
Supongamos que
\[ 0 ≤ b - a  \tag{1} \]
La demostración se tiene por la siguiente cadena de desigualdades:
\begin{align}
   a &= 0 + a          &&\text{[por L1]} \\
     &≤ (b - a) + a    &&\text{[por (1) y L2]} \\
     &= b              &&\text{[por L3]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

-- 1ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by
  intro h
  calc
    a = 0 + a       := (zero_add a).symm
    _ ≤ (b - a) + a := add_le_add_right h a
    _ = b           := sub_add_cancel b a

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by apply?
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
by simp

-- Lemas usados
-- ============

-- #check (zero_add a : 0 + a = a)
-- #check (add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a)
-- #check (sub_add_cancel a b : a - b + b = a)
-- #check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_sobre_anillos_ordenados_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 22.</li>
</ul>
