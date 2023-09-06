---
Título: En los retículos, x ⊔ (x ⊓ y) = x
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los retículos se verifica que
\[ x ⊔ (x ⊓ y) = x \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]--
variable (x y : α)

example : x ⊔ (x ⊓ y) = x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
En la demostración se usarán los siguientes lemas
\begin{align}
  &x ≤ y → y ≤ x → x = y       \tag{L1} \\
  &x ⊓ y ≤ x                   \tag{L2} \\
  &x ≤ x                       \tag{L3} \\
  &x ≤ x ⊔ y                   \tag{L4} \\
  &x ≤ z → y ≤ z → x ⊔ y ≤ z   \tag{L5}
\end{align}

Por L1, basta demostrar las siguientes relaciones:
\begin{align}
   &x ⊔ (x ⊓ y) ≤ x    \tag{1} \\
   &x ≤ x ⊔ (x ⊓ y)    &&\text{[que se tiene por L4]}
\end{align}

Para demostrar (1), por L5, basta probar las relaciones:
\begin{align}
   &x ≤ x              &&\text{[que se tiene por L3]} \\
   &x ⊓ y ≤ x          &&\text{[que se tiene por L2]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]--
variable (x y : α)

-- 1ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  have h1 : x ⊔ (x ⊓ y) ≤ x
  { have h1a : x ≤ x := le_rfl
    have h1b : x ⊓ y ≤ x := inf_le_left
    show x ⊔ (x ⊓ y) ≤ x
    exact sup_le h1a h1b }
  have h2 : x ≤ x ⊔ (x ⊓ y) := le_sup_left
  show x ⊔ (x ⊓ y) = x
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  have h1 : x ⊔ (x ⊓ y) ≤ x := by simp
  have h2 : x ≤ x ⊔ (x ⊓ y) := by simp
  show x ⊔ (x ⊓ y) = x
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by
  apply le_antisymm
  . -- x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    . -- x ≤ x
      apply le_rfl
    . -- x ⊓ y ≤ x
      apply inf_le_left
  . -- x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by apply?
sup_inf_self

-- 5ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
by simp

-- Lemas usados
-- ============

-- variable (z : α)
-- #check (le_rfl : x ≤ x)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (sup_inf_self : x ⊔ (x ⊓ y) = x)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Leyes_de_absorcion_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 21.</li>
</ul>
