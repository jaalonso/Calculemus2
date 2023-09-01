---
Título: En los retículos, x ⊔ y = y ⊔ x
Autor:  José A. Alonso
---

Demostrar con Lean4 que en los retículos se verifica que
\[x ⊔ y = y ⊔ x\]
para todo \(x\) e \(y\) en el retículo.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

example : x ⊔ y = y ⊔ x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Es consecuencia del siguiente lema auxiliar
\[   (∀ a, b)[a ⊔ b ≤ b ⊔ a] \tag{1} \]
En efecto, sustituyendo en (1) \(a\) por \(x\) y \(b\) por \(y\), se tiene
\[   x ⊔ y ≤ y ⊔ x \tag{2} \]
y sustituyendo en (1) \(a\) por \(y\) y \(b\) por \(x\), se tiene
\[   y ⊔ x ≤ x ⊔ y \tag{3} \]
Finalmente, aplicando la propiedad antisimétrica de la divisibilidad
a (2) y (3), se tiene
\[   x ⊔ y = y ⊔ x \]

Para demostrar (1), por la definición del supremo, basta demostrar las siguientes relaciones
\begin{align}
   x &≤ y ⊔ x \\
   y &≤ y ⊔ x
\end{align}
y ambas se tienen por la definición del supremo.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración del lema auxiliar
lemma aux : x ⊔ y ≤ y ⊔ x :=
by
  have h1 : x ≤ y ⊔ x :=
    le_sup_right
  have h2 : y ≤ y ⊔ x :=
    le_sup_left
  show x ⊔ y ≤ y ⊔ x
  exact sup_le h1 h2

-- 2ª demostración del lema auxiliar
example : x ⊔ y ≤ y ⊔ x :=
by
  apply sup_le
  { apply le_sup_right }
  { apply le_sup_left }

-- 3ª demostración del lema auxiliar
example : x ⊔ y ≤ y ⊔ x :=
sup_le le_sup_right le_sup_left

-- 1ª demostración
example : x ⊔ y = y ⊔ x :=
by
  have h1 : x ⊔ y ≤ y ⊔ x :=
    aux x y
  have h2 : y ⊔ x ≤ x ⊔ y :=
    aux y x
  show x ⊔ y = y ⊔ x
  exact le_antisymm h1 h2

-- 2ª demostración
example : x ⊔ y = y ⊔ x :=
by
  apply le_antisymm
  { apply aux }
  { apply aux }

-- 3ª demostración
example : x ⊔ y = y ⊔ x :=
le_antisymm (aux x y) (aux y x)

-- 4ª demostración
example : x ⊔ y = y ⊔ x :=
by apply le_antisymm; simp ; simp

-- 5ª demostración
example : x ⊔ y = y ⊔ x :=
-- by apply?
sup_comm

-- Lemas usados
-- ============

-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (sup_comm : x ⊔ y = y ⊔ x)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Conmutatividad_del_supremo.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 20.</li>
</ul>
