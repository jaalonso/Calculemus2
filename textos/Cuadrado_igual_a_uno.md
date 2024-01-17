---
Título: En ℝ, si x² = 1 entonces x = 1 ó x = -1.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \(ℝ\), si \(x² = 1\) entonces \(x = 1\) ó \(x = -1\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by sorry
</pre>
<!--more-->

<h2>Demostración en lenguaje natural</h2>

Usaremos los siguientes lemas
\begin{align}
   &(∀ x ∈ ℝ)[x - x = 0]                                           \tag{L1} \\
   &(∀ x, y ∈ ℝ)[xy = 0 → x = 0 ∨ y = 0]                           \tag{L2} \\
   &(∀ x, y ∈ ℝ)[x - y = 0 ↔ x = y]                                \tag{L3} \\
   &(∀ x, y ∈ ℝ)[x + y = 0 → x = -y]                               \tag{L4}
\end{align}

Se tiene que
\begin{align}
   (x - 1)(x + 1) &= x² - 1     \\
                  &= 1 - 1      &&\text{[por la hipótesis]} \\
                  &= 0          &&\text{[por L1]}
\end{align}
y, por el lema L2, se tiene que
\[ x - 1 = 0 ∨ x + 1 = 0 \]
Acabaremos la demostración por casos.

Primer caso:
\begin{align}
  x - 1 = 0 &⟹ x = 1             &&\text{[por L3]} \\
            &⟹ x = 1 ∨ x = -1
\end{align}

Segundo caso:
\begin{align}
  x + 1 = 0 &⟹ x = -1            &&\text{[por L4]} \\
            &⟹ x = 1 ∨ x = -1
\end{align}

<h2>Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by
  have h1 : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x^2 - 1 := by ring
                         _ = 1 - 1   := by rw [h]
                         _ = 0       := sub_self 1
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  . -- h3 : x - 1 = 0
    left
    -- ⊢ x = 1
    exact sub_eq_zero.mp h3
  . -- h4 : x + 1 = 0
    right
    -- ⊢ x = -1
    exact eq_neg_of_add_eq_zero_left h4

-- 2ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by
  have h1 : (x - 1) * (x + 1) = 0 := by nlinarith
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := by aesop
  rcases h2 with h3 | h4
  . -- h3 : x - 1 = 0
    left
    -- ⊢ x = 1
    linarith
  . -- h4 : x + 1 = 0
    right
    -- ⊢ x = -1
    linarith

-- 3ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
sq_eq_one_iff.mp h

-- 3ª demostración
-- ===============

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
by aesop

-- Lemas usados
-- ============

-- #check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
-- #check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
-- #check (sq_eq_one_iff : x ^ 2 = 1 ↔ x = 1 ∨ x = -1)
-- #check (sub_eq_zero : x - y = 0 ↔ x = y)
-- #check (sub_self x : x - x = 0)
</pre>

<h2>Demostraciones interactivas</h2>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cuadrado_igual_a_uno.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>Referencias</h2>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>

<h2>Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Cuadrado_igual_a_uno
  imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 ∨ x = -1"
proof -
  have "(x - 1) * (x + 1) = x^2 - 1"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - 1) * (x + 1) = 0" .
  moreover
  { assume "(x - 1) = 0"
    then have "x = 1"
      by simp }
  moreover
  { assume "(x + 1) = 0"
    then have "x = -1"
      by simp }
  ultimately show "x = 1 ∨ x = -1"
    by auto
qed

(* 2ª demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 ∨ x = -1"
proof -
  have "(x - 1) * (x + 1) = x^2 - 1"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - 1) * (x + 1) = 0" .
  then show "x = 1 ∨ x = -1"
    by auto
qed

(* 3ª demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 ∨ x = -1"
proof -
  have "(x - 1) * (x + 1) = 0"
  proof -
    have "(x - 1) * (x + 1) = x^2 - 1" by algebra
    also have "… = 0" by (simp add: assms)
    finally show ?thesis .
  qed
  then show "x = 1 ∨ x = -1"
    by auto
qed

(* 4ª demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 ∨ x = -1"
using assms power2_eq_1_iff by blast

end
</pre>
