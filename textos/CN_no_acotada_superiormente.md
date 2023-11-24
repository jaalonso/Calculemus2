---
Título: Si f no está acotada superiormente, entonces (∀a)(∃x)[f(x) > a]
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) no está acotada superiormente, entonces \\((∀a)(∃x)[f(x) > a]​\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

example
  (h : ¬acotadaSup f)
  : ∀ a, ∃ x, f x > a :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

<b>1ª demostración en LN</b>

Usaremos los siguientes lemas
\\begin{align}
   &¬(∃x)P(x) → (∀x)¬P(x) \\tag{L1} \\\\
   &¬a > b → a ≤ b        \\tag{L2}
\\end{align}

Sea \\(a ∈ ℝ\\). Tenemos que demostrar que
\\[ (∃x)[f(x) > a] \\]
Lo haremos por reducción al absurdo. Para ello, suponemos que
\\[ ¬(∃x)[f(x) > a] \\tag{1} \\]
y tenemos que obtener una contradicción. Aplicando L1 a (1) se tiene
\\[ (∀x)[¬ f(x) > a] \\]
y, aplicando L2, se tiene
\\[ (∀x)[f(x) ≤ a] \\]
Lo que significa que \\(a\\) es una cota superior de \\(f\\) y, por tanto \\(f\\) está acotada superiormente, en cotradicción con la hipótesis.

<b>2ª demostración en LN</b>

Por la contrarecíproca, se supone que
\\[ ¬(∀a)(∃x)[f(x) > a] \\tag{1} \\]
y tenemos que demostrar que \\(f\\) está acotada superiormente.

Interiorizando la negación en (1) y simplificando, se tiene que
\\[ (∃a)(∀x)[f x ≤ a] \\]
que es lo que teníamos que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬acotadaSup f)
  : ∀ a, ∃ x, f x > a :=
by
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, f x > a
  by_contra h1
  -- h1 : ¬∃ x, f x > a
  -- ⊢ False
  have h2 : ∀ x, ¬ f x > a :=
    forall_not_of_not_exists h1
  have h3 : ∀ x, f x ≤ a := by
    intro x
    have h3a : ¬ f x > a := h2 x
    show f x ≤ a
    exact le_of_not_gt h3a
  have h4 : CotaSuperior f a := h3
  have h5 : ∃ b, CotaSuperior f b := ⟨a, h4⟩
  have h6 : acotadaSup f := h5
  show False
  exact h h6

-- 2ª demostración
-- ===============

example
  (h : ¬acotadaSup f)
  : ∀ a, ∃ x, f x > a :=
by
  intro a
  -- a : ℝ
  -- ⊢ ∃ x, f x > a
  by_contra h1
  -- h1 : ¬∃ x, f x > a
  -- ⊢ False
  apply h
  -- ⊢ acotadaSup f
  use a
  -- ⊢ CotaSuperior f a
  intro x
  -- x : ℝ
  -- ⊢ f x ≤ a
  apply le_of_not_gt
  -- ⊢ ¬f x > a
  intro h2
  -- h2 : f x > a
  -- ⊢ False
  apply h1
  -- ⊢ ∃ x, f x > a
  use x
  -- ⊢ f x > a
  exact h2

-- 3ª demostración
-- ===============

example
  (h : ¬acotadaSup f)
  : ∀ a, ∃ x, f x > a :=
by
  unfold acotadaSup at h
  -- h : ¬∃ a, CotaSuperior f a
  unfold CotaSuperior at h
  -- h : ¬∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- ∀ (a : ℝ), ∃ x, f x > a
  exact h

-- 4ª demostración
-- ===============

example
  (h : ¬acotadaSup f)
  : ∀ a, ∃ x, f x > a :=
by
  simp only [acotadaSup, CotaSuperior] at h
  -- h : ¬∃ a, ∀ (x : ℝ), f x ≤ a
  push_neg at h
  -- ∀ (a : ℝ), ∃ x, f x > a
  exact h

-- 5ª demostración
-- ===============

example
  (h : ¬acotadaSup f) :
  ∀ a, ∃ x, f x > a :=
by
  contrapose h
  -- h : ¬∀ (a : ℝ), ∃ x, f x > a
  -- ⊢ ¬¬acotadaSup f
  push_neg at *
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  -- ⊢ acotadaSup f
  exact h

-- 6ª demostración
-- ===============

example
  (h : ¬acotadaSup f) :
  ∀ a, ∃ x, f x > a :=
by
  contrapose! h
  -- h : ∃ a, ∀ (x : ℝ), f x ≤ a
  -- ⊢ acotadaSup f
  exact h

-- Lemas usados
-- ============

-- variable {α : Type _}
-- variable (P : α → Prop)
-- #check (forall_not_of_not_exists : (¬∃ x, P x) → ∀ x, ¬P x)
--
-- variable (a b : ℝ)
-- #check (le_of_not_gt : ¬a > b → a ≤ b)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CN_no_acotada_superiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 33.</li>
</ul>
