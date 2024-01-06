---
Título: Si ≤ es un preorden, entonces < es transitiva.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(≤\\) es un preorden, entonces \\(<\\) es transitiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a b c : α)

example : a < b → b < c → a < c :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usará la siguiente propiedad de los preórdenes
\\[ (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a] \\]
Con dicha propiedad, lo que tenemos que demostrar se transforma en
\\[ a ≤ b ∧ b ≰ a → b ≤ c ∧ c ≰ b → a ≤ c ∧ c ≰ a \\]
Para demostrarla, supongamos que
\\begin{align}
   &a ≤ b \\tag{(1)} \\\\
   &b ≰ a \\tag{(2)} \\\\
   &b ≤ c \\tag{(3)} \\\\
   &c ≰ b \\tag{(4)}
\\end{align}
y tenemos que demostrar las siguientes relaciones
\\begin{align}
   &a ≤ c \\tag{(5)} \\\\
   &c ≰ a \\tag{(6)}
\\end{align}

La (5) se tiene aplicando la propiedad transitiva a (1) y (3).

Para demostrar la (6), supongamos que
\\[ c ≤ a \\tag{(7)} \\]
entonces, junto a la (1), por la propieda transitiva se tiene
\\[ c ≤ b \\]
que es una contradicción con la (4).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [Preorder α]
variable (a b c : α)

-- 1ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    contrapose! h4
    -- h4 : c ≤ a
    -- ⊢ c ≤ b
    exact le_trans h4 h1

-- 2ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    rintro (h5 : c ≤ a)
    -- ⊢ False
    have h6 : c ≤ b := le_trans h5 h1
    show False
    exact h4 h6

-- 3ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  constructor
  . -- ⊢ a ≤ c
    exact le_trans h1 h3
  . -- ⊢ ¬c ≤ a
    exact fun h5 ↦ h4 (le_trans h5 h1)

-- 4ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h1 : a ≤ b, _h2 : ¬b ≤ a⟩ ⟨h3 : b ≤ c, h4 : ¬c ≤ b⟩
  -- ⊢ a ≤ c ∧ ¬c ≤ a
  exact ⟨le_trans h1 h3, fun h5 ↦ h4 (le_trans h5 h1)⟩

-- 5ª demostración
-- ===============

example : a < b → b < c → a < c :=
by
  simp only [lt_iff_le_not_le]
  -- ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  exact fun ⟨h1, _h2⟩ ⟨h3, h4⟩ ↦ ⟨le_trans h1 h3,
                                  fun h5 ↦ h4 (le_trans h5 h1)⟩

-- 6ª demostración
-- ===============

example : a < b → b < c → a < c :=
  lt_trans

-- Lemas usados
-- ============

-- #check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- #check (lt_trans : a < b → b < c → a < c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Preorden_transitiva.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 38.</li>
</ul>
