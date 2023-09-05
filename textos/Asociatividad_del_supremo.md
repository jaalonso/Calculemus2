---
Título: En los retículos, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los retículos se verifica que
\[ (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice

variable {α : Type _} [Lattice α]
variable (x y z : α)

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
En la demostración se usarán los siguientes lemas
\begin{align}
   &x ≤ y → y ≤ x → x = y     \tag{L1} \label{L1} \\
   &x ≤ x ⊔ y                 \tag{L2} \label{L2} \\
   &y ≤ x ⊔ y                 \tag{L3} \label{L3} \\
   &x ≤ z → y ≤ z → x ⊔ y ≤ z \tag{L4} \label{L4} \\
\end{align}

Por \ref{L1}, basta demostrar las siguientes relaciones:
\begin{align}
   (x ⊔ y) ⊔ z &≤ x ⊔ (y ⊔ z)  \tag{1} \label{1} \\
   x ⊔ (y ⊔ z) &≤ (x ⊔ y) ⊔ z  \tag{2} \label{2}
\end{align}

Para demostrar (\ref{1}), por \ref{L4}, basta probar
\begin{align}
   x ⊔ y &≤ x ⊔ (y ⊔ z) \tag{1a} \label{1a} \\
       z &≤ x ⊔ (y ⊔ z) \tag{1b} \label{1b}
\end{align}

Para demostrar (\ref{1a}), por \ref{L4}, basta probar
\begin{align}
   x &≤ x ⊔ (y ⊔ z) \tag{1a1} \label{1a1} \\
   y &≤ x ⊔ (y ⊔ z) \tag{1a2} \label{1a2}
\end{align}

La (\ref{1a1}) se tiene por \ref{L2}.

La (\ref{1a2}) se tiene por la siguiente cadena de desigualdades:
\begin{align}
   y &≤ y ⊔ z          &&\text{[por \ref{L2}]} \\
     &≤ x ⊔ (y ⊔ z)    &&\text{[por \ref{L3}]}
\end{align}

La (\ref{1b}) se tiene por la siguiente cadena de desigualdades
\begin{align}
   z &≤ y ⊔ z          &&\text{[por \ref{L3}]} \\
     &≤ x ⊔ (y ⊔ z)    &&\text{[por \ref{L3}]}
\end{align}

Para demostrar (\ref{2}), por \ref{L4}, basta probar
\begin{align}
       x &≤ (x ⊔ y) ⊔ z  \tag{2a} \label{2a} \\
   y ⊔ z &≤ (x ⊔ y) ⊔ z  \tag{2b} \label{2b}
\end{align}

La (\ref{2a}) se demuestra por la siguiente cadena de desigualdades:
\begin{align}
   x &≤ x ⊔ y          &&\text{[por \ref{L2}]} \\
     &≤ (x ⊔ y) ⊔ z    &&\text{[por \ref{L2}]}
\end{align}

Para demostrar (\ref{2b}), por \ref{L4}, basta probar
\begin{align}
   y &≤ (x ⊔ y) ⊔ z \tag{2b1} \label{2b1} \\
   z &≤ (x ⊔ y) ⊔ z \tag{2b2} \label{2b2}
\end{align}

La (\ref{2b1}) se demuestra por la siguiente cadena de desigualdades:
\begin{align}
   y &≤ x ⊔ y          &&\text{[por \ref{L3}]} \\
     &≤ (x ⊔ y) ⊔ z    &&\text{[por \ref{L2}]}
\end{align}

La (\ref{2b2}) se tiene por \ref{L3}.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice

variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  have h1 : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z) := by
  { have h1a : x ⊔ y ≤ x ⊔ (y ⊔ z) := by
    { have h1a1 : x ≤ x ⊔ (y ⊔ z) := by exact le_sup_left
      have h1a2 : y ≤ x ⊔ (y ⊔ z) := calc
        y ≤ y ⊔ z       := by exact le_sup_left
        _ ≤ x ⊔ (y ⊔ z) := by exact le_sup_right
      show x ⊔ y ≤ x ⊔ (y ⊔ z)
      exact sup_le h1a1 h1a2 }
    have h1b : z ≤ x ⊔ (y ⊔ z) := calc
      z ≤ y ⊔ z       := by exact le_sup_right
      _ ≤ x ⊔ (y ⊔ z) := by exact le_sup_right
    show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    exact sup_le h1a h1b }
  have h2 : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z := by
  { have h2a : x ≤ (x ⊔ y) ⊔ z := calc
      x ≤ x ⊔ y       := by exact le_sup_left
      _ ≤ (x ⊔ y) ⊔ z := by exact le_sup_left
    have h2b : y ⊔ z ≤ (x ⊔ y) ⊔ z := by
    { have h2b1 : y ≤ (x ⊔ y) ⊔ z := calc
        y ≤ x ⊔ y       := by exact le_sup_right
        _ ≤ (x ⊔ y) ⊔ z := by exact le_sup_left
      have h2b2 : z ≤ (x ⊔ y) ⊔ z := by
        exact le_sup_right
      show  y ⊔ z ≤ (x ⊔ y) ⊔ z
      exact sup_le h2b1 h2b2 }
    show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    exact sup_le h2a h2b }
  show (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  · -- (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · -- x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      . -- x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      · -- y ≤ x ⊔ (y ⊔ z)
        apply le_trans
        . -- y ≤ y ⊔ z
          apply @le_sup_left _ _ y z
        . -- y ⊔ z ≤ x ⊔ (y ⊔ z)
          apply le_sup_right
    . -- z ≤ x ⊔ (y ⊔ z)
      apply le_trans
      . -- z ≤ x ⊔ (y ⊔ z)
        apply @le_sup_right _ _ y z
      . -- y ⊔ z ≤ x ⊔ (y ⊔ z)
        apply le_sup_right
  . -- x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    apply sup_le
    · -- x ≤ (x ⊔ y) ⊔ z
      apply le_trans
      . -- x ≤ x ⊔ y
        apply @le_sup_left _ _ x y
      . -- x ⊔ y ≤ (x ⊔ y) ⊔ z
        apply le_sup_left
    . -- y ⊔ z ≤ (x ⊔ y) ⊔ z
      apply sup_le
      · -- y ≤ (x ⊔ y) ⊔ z
        apply le_trans
        . -- y ≤ x ⊔ y
          apply @le_sup_right _ _ x y
        . -- x ⊔ y ≤ (x ⊔ y) ⊔ z
          apply le_sup_left
      . -- z ≤ (x ⊔ y) ⊔ z
        apply le_sup_right

-- 3ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      . apply le_sup_left
      · apply le_trans
        . apply @le_sup_left _ _ y z
        . apply le_sup_right
    . apply le_trans
      . apply @le_sup_right _ _ y z
      . apply le_sup_right
  . apply sup_le
    · apply le_trans
      . apply @le_sup_left _ _ x y
      . apply le_sup_left
    . apply sup_le
      · apply le_trans
        . apply @le_sup_right _ _ x y
        . apply le_sup_left
      . apply le_sup_right

-- 4ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  . -- (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    . -- x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le le_sup_left (le_sup_of_le_right le_sup_left)
    . -- z ≤ x ⊔ (y ⊔ z)
      apply le_sup_of_le_right le_sup_right
  . -- x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    apply sup_le
    . -- x ≤ (x ⊔ y) ⊔ z
      apply le_sup_of_le_left le_sup_left
    . -- y ⊔ z ≤ (x ⊔ y) ⊔ z
      apply sup_le (le_sup_of_le_left le_sup_right) le_sup_right

-- 5ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  apply le_antisymm
  . apply sup_le
    . apply sup_le le_sup_left (le_sup_of_le_right le_sup_left)
    . apply le_sup_of_le_right le_sup_right
  . apply sup_le
    . apply le_sup_of_le_left le_sup_left
    . apply sup_le (le_sup_of_le_left le_sup_right) le_sup_right

-- 6ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
    (le_sup_of_le_right le_sup_right))
  (sup_le
    (le_sup_of_le_left le_sup_left)
    (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))

-- 7ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
-- by apply?
sup_assoc

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_of_le_left : z ≤ x → z ≤ x ⊔ y)
-- #check (le_sup_of_le_right : z ≤ y → z ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (sup_assoc : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z))
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Asociatividad_del_supremo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 21.</li>
</ul>
