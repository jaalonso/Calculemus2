---
Título: Si r ⊆ s y s ⊆ t, entonces r ⊆ t
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(r ⊆ s\\) y \\(s ⊆ t\\), entonces \\(r ⊆ t\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Set

variable {α : Type _}
variable (r s t : Set α)

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
<b>1ª demostración en LN</b>

Tenemos que demostrar que
\\[ (∀ x) [x ∈ r → x ∈ t] \\]
Sea \\(x\\) tal que
\\[ x ∈ r \\]
Puesto que \\(r ⊆ s\\), se tiene que
\\[ x ∈ s \\]
y, puesto que \\(s ⊆ t), se tiene que
\\[ x ∈ t \\]
que es lo que teníamos que demostrar.

<b>2ª demostración en LN</b>

Tenemos que demostrar que
\\[ (∀ x) [x ∈ r → x ∈ t] \\]
Sea \\(x\\) tal que
\\[ x ∈ r \\]
Tenemos que demostrar que
\\[ x ∈ t \\]
que, puesto que \\(s ⊆ t\\), se reduce a
\\[ x ∈ s \\]
que, puesto que \\(r ⊆ s\\), se redece a
\\[ x ∈ r \\]
que es lo que hemos supuesto.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

open Set

variable {α : Type _}
variable (r s t : Set α)

-- 1ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by
  intros x xr
  -- xr : x ∈ r
  have xs : x ∈ s := rs xr
  show x ∈ t
  exact st xs

-- 2ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by
  intros x xr
  -- x : α
  -- xr : x ∈ r
  apply st
  -- ⊢ x ∈ s
  apply rs
  -- ⊢ x ∈ r
  exact xr

-- 3ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
fun _ xr ↦ st (rs xr)

-- 4ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by exact?
Subset.trans rs st

-- 5ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by tauto

-- Lemas usados
-- ============

-- #check (Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_transitiva_del_subconjunto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 27.</li>
</ul>
