---
Título: En los retículos, x ⊓ (x ⊔ y) = x
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los retículos se verifica que
\[ x ⊓ (x ⊔ y) = x \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y : α)

example : x ⊓ (x ⊔ y) = x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
En la demostración se usarán los siguientes lemas
\begin{align}
   &x ≤ y → y ≤ x → x = y      \tag{L1} \\
   &x ⊓ y ≤ x                  \tag{L2} \\
   &z ≤ x → z ≤ y → z ≤ x ⊓ y  \tag{L3} \\
   &x ≤ x                      \tag{L4} \\
   &x ≤ x ⊔ y                  \tag{L5} \\
\end{align}

Por L1, basta demostrar las siguientes relaciones:
\begin{align}
   x ⊓ (x ⊔ y) &≤ x           \tag{1} \\
             x &≤ x ⊓ (x ⊔ y) \tag{2}
\end{align}

La (1) se tiene por L2.

Para demostrar la (2), por L3, basta probar las relaciones:
\begin{align}
   x &≤ x       \tag{2a} \\
   x &≤ x ⊔ y   \tag{2b}
\end{align}

La (2a) se tiene por L4.

La (2b) se tiene por L5

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y : α)

-- 1ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  have h1 : x ⊓ (x ⊔ y) ≤ x := inf_le_left
  have h2 : x ≤ x ⊓ (x ⊔ y)
  { have h2a : x ≤ x := le_rfl
    have h2b : x ≤ x ⊔ y := le_sup_left
    show x ≤ x ⊓ (x ⊔ y)
    exact le_inf h2a h2b }
  show x ⊓ (x ⊔ y) = x
  exact le_antisymm h1 h2

-- 2ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  have h1 : x ⊓ (x ⊔ y) ≤ x := by simp
  have h2 : x ≤ x ⊓ (x ⊔ y) := by simp
  show x ⊓ (x ⊔ y) = x
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by
  apply le_antisymm
  . -- x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . -- x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . -- x ≤ x
      apply le_rfl
    . -- x ≤ x ⊔ y
      apply le_sup_left

-- 4ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
le_antisymm inf_le_left (le_inf le_rfl le_sup_left)

-- 5ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
-- by apply?
inf_sup_self

-- 6ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
by simp

-- Lemas usados
-- ============

-- variable (z : α)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_sup_self : x ⊓ (x ⊔ y) = x)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
-- #check (le_rfl : x ≤ x)
-- #check (le_sup_left : x ≤ x ⊔ y)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Leyes_de_absorcion_1.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 21.</li>
</ul>
