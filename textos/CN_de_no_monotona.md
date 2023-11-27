---
Título: Si f no es monótona, entonces ∃x∃y[x ≤ y ∧ f(y) < f(x)]​.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) no es monótona, entonces ()∃x∃y[x ≤ y ∧ f(y) < f(x)]​\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable (f : ℝ → ℝ)

example
  (h : ¬Monotone f)
  : ∃ x y, x ≤ y ∧ f y < f x :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Usaremos los siguientes lemas:
\\begin{align}
   &¬(∀x)P(x) ↔ (∃ x)¬P(x)      \\tag{L1} \\\\
   &¬(p → q) ↔ p ∧ ¬q           \\tag{L2} \\\\
   &(∀a, b ∈ ℝ)[¬b ≤ a → a < b] \\tag{L3}
\\end{align}

Por la definición de función monótona,
\\[ ¬(∀x)(∀y)[x ≤ y → f(x) ≤ f(y)] \\]
Aplicando L1 se tiene
\\[ (∃x)¬(∀y)[x ≤ y → f(x) ≤ f(y)] \\]
Sea \\(a\\) tal que
\\[ ¬(∀y)[a ≤ y → f(a) ≤ f(y)] \\]
Aplicando L1 se tiene
\\[ (∃y)¬[a ≤ y → f(a) ≤ f(y)] \\]
Sea \\(b\\) tal que
\\[ ¬[a ≤ b → f(a) ≤ f(b)] \\]
Aplicando L2 se tiene que
\\[ a ≤ b ∧ ¬(f(a) ≤ f(b)) \\]
Aplicando L3 se tiene que
\\[ a ≤ b ∧ f(b) < f(a) \\]
Por tanto,
\\[ (∃x,y)[x ≤ y ∧ f(y) < f(x)] \\]

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ¬Monotone f)
  : ∃ x y, x ≤ y ∧ f y < f x :=
by
  have h1 : ¬∀ x y, x ≤ y → f x ≤ f y := h
  have h2 : ∃ x, ¬(∀ y, x ≤ y → f x ≤ f y) := not_forall.mp h1
  rcases h2 with ⟨a, ha : ¬∀ y, a ≤ y → f a ≤ f y⟩
  have h3 : ∃ y, ¬(a ≤ y → f a ≤ f y) := not_forall.mp ha
  rcases h3 with ⟨b, hb : ¬(a ≤ b → f a ≤ f b)⟩
  have h4 : a ≤ b ∧ ¬(f a ≤ f b) := not_imp.mp hb
  have h5 : a ≤ b ∧ f b < f a := ⟨h4.1, lt_of_not_le h4.2⟩
  use a, b
  -- ⊢ a ≤ b ∧ f b < f a
  exact h5

-- 2ª demostración
-- ===============

example
  (h : ¬Monotone f)
  : ∃ x y, x ≤ y ∧ f y < f x :=
by
  simp only [Monotone] at h
  -- h : ¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b
  push_neg at h
  -- h : Exists fun ⦃a⦄ => Exists fun ⦃b⦄ => a ≤ b ∧ f b < f a
  exact h

-- Lemas usados
-- ============

-- variable {α : Type _}
-- variable (P : α → Prop)
-- variable (p q : Prop)
-- variable (a b : ℝ)
-- #check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
-- #check (not_imp : ¬(p → q) ↔ p ∧ ¬q)
-- #check (lt_of_not_le : ¬b ≤ a → a < b)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CN_de_no_monotona.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 34.</li>
</ul>
