---
Título: En los retículos, una distributiva del supremos implica la otra
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(R\) es un retículo tal que
\[   (∀ x,\ y,\ z \in α) [x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)] \]
entonces
\[   (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) \]
para todos los elementos del retículo.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (a b c : α)

example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se demuestra por la siguiente cadena de igualdades
\begin{align}
   (a ⊓ b) ⊔ c &= c ⊔ (a ⊓ b)          &&\text{[por la conmutatividad de ⊔]} \\
               &= (c ⊔ a) ⊓ (c ⊔ b)    &&\text{[por la hipótesis]} \\
               &= (a ⊔ c) ⊓ (c ⊔ b)    &&\text{[por la conmutatividad de ⊔]} \\
               &= (a ⊔ c) ⊓ (b ⊔ c)    &&\text{[por la conmutatividad de ⊔]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (a b c : α)

-- 1ª demostración
example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
calc
  (a ⊓ b) ⊔ c = c ⊔ (a ⊓ b)       := by rw [sup_comm]
            _ = (c ⊔ a) ⊓ (c ⊔ b) := by rw [h]
            _ = (a ⊔ c) ⊓ (c ⊔ b) := by rw [@sup_comm _ _ c a]
            _ = (a ⊔ c) ⊓ (b ⊔ c) := by rw [@sup_comm _ _ c b]

-- 2ª demostración
example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
by simp [h, sup_comm]

-- Lemas usados
-- ============

-- #check (sup_comm : a ⊔ b = b ⊔ a)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_distributiva_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 22.</li>
</ul>
