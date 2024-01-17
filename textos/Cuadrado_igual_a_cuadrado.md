---
Título: En ℝ, x² = y² → x = y ∨ x = -y.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que en \(ℝ\),
\[x² = y² → x = y ∨ x = -y\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Usaremos los siguientes lemas
\begin{align}
   &(∀ x ∈ ℝ)[x - x = 0]                                           \tag{L1} \\
   &(∀ x, y ∈ ℝ)[xy = 0 → x = 0 ∨ y = 0]                           \tag{L2} \\
   &(∀ x, y ∈ ℝ)[x - y = 0 ↔ x = y]                                \tag{L3} \\
   &(∀ x, y ∈ ℝ)[x + y = 0 → x = -y]                               \tag{L4}
\end{align}

Se tiene que
\begin{align}
   (x - y)(x + y) &= x² - y²    \\
                  &= y² - y²    &&\text{[por la hipótesis]} \\
                  &= 0          &&\text{[por L1]}
\end{align}
y, por el lema L2, se tiene que
\[ x - y = 0 ∨ x + y = 0 \]

Acabaremos la demostración por casos.

Primer caso:
\begin{align}
  x - y = 0 &⟹ x = y             &&\text{[por L3]} \\
            &⟹ x = y ∨ x = -y
\end{align}

Segundo caso:
\begin{align}
  x + y = 0 &⟹ x = -y            &&\text{[por L4]} \\
            &⟹ x = y ∨ x = -y
\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by
  have h1 : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x^2 - y^2 := by ring
                         _ = y^2 - y^2 := by rw [h]
                         _ = 0         := sub_self (y ^ 2)
  have h2 : x - y = 0 ∨ x + y = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  . -- h3 : x - y = 0
    left
    -- ⊢ x = y
    exact sub_eq_zero.mp h3
  . -- h4 : x + y = 0
    right
    -- ⊢ x = -y
    exact eq_neg_of_add_eq_zero_left h4

-- 2ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by
  have h1 : (x - y) * (x + y) = 0 := by nlinarith
  have h2 : x - y = 0 ∨ x + y = 0 := by aesop
  rcases h2 with h3 | h4
  . -- h3 : x - y = 0
    left
    -- ⊢ x = y
    linarith
  . -- h4 : x + y = 0
    right
    -- ⊢ x = -y
    linarith

-- 2ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
sq_eq_sq_iff_eq_or_eq_neg.mp h

-- Lemas usados
-- ============

-- #check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
-- #check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
-- #check (sq_eq_sq_iff_eq_or_eq_neg : x ^ 2 = y ^ 2 ↔ x = y ∨ x = -y)
-- #check (sub_eq_zero : x - y = 0 ↔ x = y)
-- #check (sub_self x : x - x = 0)
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cuadrado_igual_a_cuadrado.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>

<h2>3. Demostraciones con Isabelle/HOL</h2>

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
