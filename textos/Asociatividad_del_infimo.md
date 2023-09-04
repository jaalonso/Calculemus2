---
Título: En los retículos, (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los retículos se verifica que
\[(x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
En la demostración se usarán los siguientes lemas:
\begin{align}
   &x ≤ y → y ≤ x → x = y     \tag{L1} \\
   &z ≤ x → z ≤ y → z ≤ x ⊓ y \tag{L2} \\
   &x ⊓ y ≤ x                 \tag{L3} \\
   &x ⊓ y ≤ y                 \tag{L4}
\end{align}

Por L1, es suficiente demostrar las siguientes relaciones:
\begin{align}
   (x ⊓ y) ⊓ z &≤ x ⊓ (y ⊓ z)   \tag{1} \\
   x ⊓ (y ⊓ z) &≤ (x ⊓ y) ⊓ z   \tag{2}
\end{align}

Para demostrar (1), por L2, basta probar que
\begin{align}
   (x ⊓ y) ⊓ z ≤ x      \tag{1a} \\
   (x ⊓ y) ⊓ z ≤ y ⊓ z  \tag{1b}
\end{align}

La (1a) se demuestra por la siguiente cadena de desigualdades
\begin{align}
   (x ⊓ y) ⊓ z &≤ x ⊓ y   &&\text{[por L3]} \\
               &≤ x       &&\text{[por L3]}
\end{align}

Para demostrar (1b), por L2, basta probar que
\begin{align}
   (x ⊓ y) ⊓ z &≤ y \tag{1b1} \\
   (x ⊓ y) ⊓ z &≤ z \tag{1b2}
\end{align}

La (1b1) se demuestra por la siguiente cadena de desigualdades
\begin{align}
   (x ⊓ y) ⊓ z &≤ x ⊓ y   &&\text{[por L3]} \\
               &≤ y       &&\text{[por L4]}
\end{align}

La (1b2) se tiene por L4.

Para demostrar (2), por L2, basta probar que
\begin{align}
   x ⊓ (y ⊓ z) &≤ x ⊓ y \tag{2a} \\
   x ⊓ (y ⊓ z) &≤ z     \tag{2b}
\end{align}

Para demostrar (2a), por L2, basta probar que
\begin{align}
   x ⊓ (y ⊓ z) &≤ x \tag{2a1} \\
   x ⊓ (y ⊓ z) &≤ y \tag{2a2}
\end{align}

La (2a1) se tiene por L3.

La (2a2) se demuestra por la siguiente cadena de desigualdades
\begin{align}
   x ⊓ (y ⊓ z) &≤ y ⊓ z   &&\text{[por L4]} \\
               &≤ y       &&\text{[por L3]}
\end{align}

La (2b) se demuestra por la siguiente cadena de desigualdades
\begin{align}
   x ⊓ (y ⊓ z) &≤ y ⊓ z   &&\text{[por L4]} \\
               &≤ z       &&\text{[por L4]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  have h1 : (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z) := by
  { have h1a : (x ⊓ y) ⊓ z ≤ x := calc
      (x ⊓ y) ⊓ z ≤ x ⊓ y := by exact inf_le_left
                _ ≤ x     := by exact inf_le_left
    have h1b : (x ⊓ y) ⊓ z ≤ y ⊓ z := by
    { have h1b1 : (x ⊓ y) ⊓ z ≤ y := calc
        (x ⊓ y) ⊓ z ≤ x ⊓ y := by exact inf_le_left
                  _ ≤ y     := by exact inf_le_right
      have h1b2 : (x ⊓ y) ⊓ z ≤ z :=
        inf_le_right
      show (x ⊓ y) ⊓ z ≤ y ⊓ z
      exact le_inf h1b1 h1b2 }
    show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    exact le_inf h1a h1b }
  have h2 : x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z := by
  { have h2a : x ⊓ (y ⊓ z) ≤ x ⊓ y := by
    { have h2a1 : x ⊓ (y ⊓ z) ≤ x :=
        inf_le_left
      have h2a2 : x ⊓ (y ⊓ z) ≤ y := calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z := by exact inf_le_right
                  _ ≤ y     := by exact inf_le_left
      show x ⊓ (y ⊓ z) ≤ x ⊓ y
      exact le_inf h2a1 h2a2 }
    have h2b : x ⊓ (y ⊓ z) ≤ z := by calc
      x ⊓ (y ⊓ z) ≤ y ⊓ z := by exact inf_le_right
                _ ≤ z     := by exact inf_le_right
    show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    exact le_inf h2a h2b }
  show (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    . apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_right
      . apply inf_le_right
  . apply le_inf
    · apply le_inf
      · apply inf_le_left
      . apply le_trans
        apply inf_le_right
        apply inf_le_left
    . apply le_trans
      apply inf_le_right
      apply inf_le_right

-- 3ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  apply le_antisymm
  . apply le_inf
    . apply inf_le_of_left_le inf_le_left
    . apply le_inf (inf_le_of_left_le inf_le_right) inf_le_right
  . apply le_inf
    . apply le_inf inf_le_left (inf_le_of_right_le inf_le_left)
    . apply inf_le_of_right_le inf_le_right

-- 4ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
le_antisymm
  (le_inf
    (inf_le_of_left_le inf_le_left)
    (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
    (inf_le_of_right_le inf_le_right))

-- 5ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by apply?
inf_assoc

-- Lemas usados
-- ============

-- #check (inf_assoc : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z))
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_of_left_le : x ≤ z → x ⊓ y ≤ z)
-- #check (inf_le_of_right_le : y ≤ z → x ⊓ y ≤ z)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Asociatividad_del_infimo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 21.</li>
</ul>
