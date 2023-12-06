---
Título: {x ≤ y, y ≰ x} ⊢ x ≤ y ∧ x ≠ y
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[\\{x ≤ y, y ≰ x\\} ⊢ x ≤ y ∧ x ≠ y\\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {x y : ℝ}

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Como la conclusión es una conjunción, tenemos que desmostrar sus  partes. La primera parte (\\(x ≤ y\\)) coincide con la hipótesis. Para demostrar la segunda parte (\\(x ≠ y\\)), supongamos que \\(x = y\\); entonces \\(y ≤ x\\) en contradicción con la segunda hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    have h4 : y ≤ x := h3.symm.le
    show False
    exact h2 h4

-- 2ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    exact h2 (h3.symm.le)

-- 3ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
⟨h1, fun h3 ↦ h2 (h3.symm.le)⟩

-- 4ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    apply h2
    -- ⊢ y ≤ x
    rw [h3]

-- 5ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  constructor
  . -- ⊢ x ≤ y
    exact h1
  . -- ⊢ x ≠ y
    intro h3
    -- h3 : x = y
    -- ⊢ False
    exact h2 (by rw [h3])

-- 6ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
⟨h1, fun h ↦ h2 (by rw [h])⟩

-- 7ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by
  have h3 : x ≠ y
  . contrapose! h2
    -- ⊢ y ≤ x
    rw [h2]
  exact ⟨h1, h3⟩

-- 8ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
by aesop
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Introduccion_de_la_conjuncion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 35.</li>
</ul>
