---
Título: Si (∃ x, y ∈ ℝ)[z = x² + y² ∨ z = x² + y² + 1], entonces z ≥ 0.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \((∃ x, y ∈ ℝ)[z = x² + y² ∨ z = x² + y² + 1]\), entonces \(z ≥ 0\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable {z : ℝ}

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by sorry
</pre>
<!--more-->

<h2>Demostración en lenguaje natural</h2>

Usaremos los siguientes lemas
\begin{align}
   &(∀ x ∈ ℝ)[x² ≥ 0]                                              \tag{L1} \\
   &(∀ x, y ∈ ℝ)[x ≥ 0 → y ≥ 0 → x + y ≥ 0]                        \tag{L2} \\
   &1 ≥ 0                                                          \tag{L3}
\end{align}

Sean \(a\) y \(b\) tales que
\[ z = a² + b² ∨ z = a² + b² + 1 \]
Entonces, por L1, se tiene que
\begin{align}
   &a² ≥ 0                                                         \tag{1} \\
   &b² ≥ 0                                                         \tag{2}
\end{align}

En el primer caso, \(z = a² + b²\) y se tiene que \(z ≥ 0\) por el lema L2 aplicado a (1) y (2).

En el segundo caso, \(z = a² + b² + 1\) y se tiene que \(z ≥ 0\) por el lema L2 aplicado a (1), (2) y L3.

<h2>Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable {z : ℝ}

-- 1ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by
  rcases h with ⟨a, b, h1⟩
  -- a b : ℝ
  -- h1 : z = a ^ 2 + b ^ 2 ∨ z = a ^ 2 + b ^ 2 + 1
  have h2 : a ^ 2 ≥ 0 := pow_two_nonneg a
  have h3 : b ^ 2 ≥ 0 := pow_two_nonneg b
  have h4 : a ^ 2 + b ^ 2 ≥ 0 := add_nonneg h2 h3
  rcases h1 with h5 | h6
  . -- h5 : z = a ^ 2 + b ^ 2
    show z ≥ 0
    calc z = a ^ 2 + b ^ 2 := h5
         _ ≥ 0             := add_nonneg h2 h3
  . -- h6 : z = a ^ 2 + b ^ 2 + 1
    show z ≥ 0
    calc z = (a ^ 2 + b ^ 2) + 1 := h6
         _ ≥ 0                   := add_nonneg h4 zero_le_one

-- 2ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by
  rcases h with ⟨a, b, h1 | h2⟩
  . -- h1 : z = a ^ 2 + b ^ 2
    have h1a : a ^ 2 ≥ 0 := pow_two_nonneg a
    have h1b : b ^ 2 ≥ 0 := pow_two_nonneg b
    show z ≥ 0
    calc z = a ^ 2 + b ^ 2 := h1
         _ ≥ 0             := add_nonneg h1a h1b
  . -- h2 : z = a ^ 2 + b ^ 2 + 1
    have h2a : a ^ 2 ≥ 0         := pow_two_nonneg a
    have h2b : b ^ 2 ≥ 0         := pow_two_nonneg b
    have h2c : a ^ 2 + b ^ 2 ≥ 0 := add_nonneg h2a h2b
    show z ≥ 0
    calc z = (a ^ 2 + b ^ 2) + 1 := h2
         _ ≥ 0                   := add_nonneg h2c zero_le_one

-- 3ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by
  rcases h with ⟨a, b, h1 | h2⟩
  . -- h1 : z = a ^ 2 + b ^ 2
    rw [h1]
    -- ⊢ a ^ 2 + b ^ 2 ≥ 0
    apply add_nonneg
    . -- ⊢ 0 ≤ a ^ 2
      apply pow_two_nonneg
    . -- ⊢ 0 ≤ b ^ 2
      apply pow_two_nonneg
  . -- h2 : z = a ^ 2 + b ^ 2 + 1
    rw [h2]
    -- ⊢ a ^ 2 + b ^ 2 + 1 ≥ 0
    apply add_nonneg
    . -- ⊢ 0 ≤ a ^ 2 + b ^ 2
      apply add_nonneg
      . -- ⊢ 0 ≤ a ^ 2
        apply pow_two_nonneg
      . -- ⊢ 0 ≤ b ^ 2
        apply pow_two_nonneg
    . -- ⊢ 0 ≤ 1
      exact zero_le_one

-- 4ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by
  rcases h with ⟨a, b, rfl | rfl⟩
  . -- ⊢ a ^ 2 + b ^ 2 ≥ 0
    apply add_nonneg
    . -- ⊢ 0 ≤ a ^ 2
      apply pow_two_nonneg
    . -- ⊢ 0 ≤ b ^ 2
      apply pow_two_nonneg
  . -- ⊢ a ^ 2 + b ^ 2 + 1 ≥ 0
    apply add_nonneg
    . -- ⊢ 0 ≤ a ^ 2 + b ^ 2
      apply add_nonneg
      . -- ⊢ 0 ≤ a ^ 2
        apply pow_two_nonneg
      . -- ⊢ 0 ≤ b ^ 2
        apply pow_two_nonneg
    . -- ⊢ 0 ≤ 1
      exact zero_le_one

-- 5ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by
  rcases h with ⟨a, b, rfl | rfl⟩
  . -- ⊢ a ^ 2 + b ^ 2 ≥ 0
    nlinarith
  . -- ⊢ a ^ 2 + b ^ 2 + 1 ≥ 0
    nlinarith

-- 6ª demostración
-- ===============

example
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)
  : z ≥ 0 :=
by rcases h with ⟨a, b, rfl | rfl⟩ <;> nlinarith

-- Lemas usados
-- ============

-- variable (x y : ℝ)
-- #check (add_nonneg : 0 ≤ x → 0 ≤ y → 0 ≤ x + y)
-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)
-- #check (zero_le_one : 0 ≤ 1)
</pre>

<h2>Demostraciones interactivas</h2>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Desigualdad_con_rcases.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>Referencias</h2>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>

<h2>Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Desigualdad_con_rcases
  imports Main "HOL.Real"
begin

(* 1ª demostración *)
lemma
  assumes "∃x y :: real. (z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)"
  shows "z ≥ 0"
proof -
  obtain x y where hxy: "z = x^2 + y^2 ∨ z = x^2 + y^2 + 1"
    using assms by auto
  { assume "z = x^2 + y^2"
    have "x^2 + y^2 ≥ 0" by simp
    then have "z ≥ 0" using `z = x^2 + y^2` by simp }
  { assume "z = x^2 + y^2 + 1"
    have "x^2 + y^2 ≥ 0" by simp
    then have "z ≥ 1" using `z = x^2 + y^2 + 1` by simp }
  with hxy show "z ≥ 0" by auto
qed

(* 2ª demostración *)
lemma
  assumes "∃x y :: real. (z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)"
  shows "z ≥ 0"
proof -
  obtain x y where hxy: "z = x^2 + y^2 ∨ z = x^2 + y^2 + 1"
    using assms by auto
  with hxy show "z ≥ 0" by auto
qed

(* 3ª demostración *)
lemma
  assumes "∃x y :: real. (z = x^2 + y^2 ∨ z = x^2 + y^2 + 1)"
  shows "z ≥ 0"
  using assms by fastforce

end
</pre>
