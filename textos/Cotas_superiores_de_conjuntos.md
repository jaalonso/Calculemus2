---
Título: Si a es una cota superior de s y a ≤ b, entonces b es una cota superior de s
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(a\\) es una cota superior de \\(s\\) y \\(a ≤ b\\), entonces \\(b\\) es una cota superior de \\(s\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {α : Type _} [PartialOrder α]
variable (s : Set α)
variable (a b : α)

-- (CotaSupConj s a) afirma que a es una cota superior del conjunto s.
def CotaSupConj (s : Set α) (a : α) :=
  ∀ {x}, x ∈ s → x ≤ a

example
  (h1 : CotaSupConj s a)
  (h2 : a ≤ b)
  : CotaSupConj s b :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Tenemos que demostrar que
\\[ (∀ x) [x ∈ s → x ≤ b] \\]
Sea \\(x\\) tal que \\(x ∈ s\\). Entonces,
\\begin{align}
   x &≤ a   &&\\text{[porque \\(a\\) es una cota superior de \\(s\\)]} \\\\
     &≤ b
\\end{align}
Por tanto, \\(x ≤ b\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

variable {α : Type _} [PartialOrder α]
variable (s : Set α)
variable (a b : α)

-- (CotaSupConj s a) afirma que a es una cota superior del conjunto s.
def CotaSupConj (s : Set α) (a : α) :=
  ∀ {x}, x ∈ s → x ≤ a

-- 1ª demostración
example
  (h1 : CotaSupConj s a)
  (h2 : a ≤ b)
  : CotaSupConj s b :=
by
  intro x (xs : x ∈ s)
  have h3 : x ≤ a := h1 xs
  show x ≤ b
  exact le_trans h3 h2

-- 2ª demostración
example
  (h1 : CotaSupConj s a)
  (h2 : a ≤ b)
  : CotaSupConj s b :=
by
  intro x (xs : x ∈ s)
  calc x ≤ a := h1 xs
       _ ≤ b := h2
-
-- Lemas usados
-- ============

-- variable (c : α)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cotas_superiores_de_conjuntos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 27.</li>
</ul>
