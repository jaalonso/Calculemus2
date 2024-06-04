---
title: Si uₙ está acotada y lim vₙ = 0, entonces lim (uₙ·vₙ) = 0
date: 2024-06-03 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(u_n\\) está acotada y \\(lim v_n = 0\\), entonces \\(lim (u_n·v_n) = 0\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a : ℝ)

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
  ∃ B, ∀ n, |a n| ≤ B

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε ∈ ℝ\\) tal que \\(ε > 0\\). Tenemos que demostrar
\\[ (∃ k)(∀ n)[n ≥ k → |(u·v)_n - 0| < ε] \\tag{1} \\]

Puesto que la sucesión \\(u\\) está acotada, existe un \\(B ∈ ℝ\\) tal que
\\[ (∀ n ∈ ℕ) |u_n| ≤ B \\tag{2} \\]
Luego \\(B ≥ 0\\). Lo demostraremos por caso según que \\(B = 0\\) ó \\(B > 0\\).

Caso 1: Supongamos que \\(B = 0\\). Entonces, por (2),
\\[ (∀ n ∈ ℕ) |u_n| ≤ 0 \\]
Luego,
\\[ (∀ n ∈ ℕ) u_n = 0 \\tag{3} \\]
Para demostrar (1), para basta tomar \\(0\\) como \\(k\\), ya que si \\(n ≥ 0\\), entonces
\\begin{align}
   |(u·v)_n - 0| &= |u_n·v_n|    \\\\
                &= |0·v_n|     &&\\text{[por (3)} \\\\
                &= 0          \\\\
                &< ε
\\w¡end{align}

Caso 2: Supongamos que \\(B > 0\\). Entonces, \\(\\dfrac{ε}{B} > 0\\) y, puesto que \\(lim v_n = 0\\), existe un \\(k ∈ ℕ\\) tal que
\\[ (∀ n)[n ≥ k → |v_n - 0| < \\dfrac{ε}{B}] \\tag{4} \\]
Para demostrar (1), para basta el mismo \\(k\\), ya que si \\(n ≥ k\\), entonces
\\begin{align}
   |(u·v)_n - 0| &= |u_n·v_n|      \\\\
                &= |u_n|·|v_n|    \\\\
                &≤ B·|v_n|       &&\\text{[por (2)]} \\\\
                &< B·\\frac{ε}{B} &&\\text{[por (4)]} \\\\
                &= ε
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a : ℝ)

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
  ∃ B, ∀ n, |a n| ≤ B

-- 1ª demostración
-- ===============

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
by
  cases' hU with B hB
  -- B : ℝ
  -- hB : ∀ (n : ℕ), |u n| ≤ B
  have hBnoneg : 0 ≤ B :=
    calc 0 ≤ |u 0| := abs_nonneg (u 0)
         _ ≤ B     := hB 0
  by_cases hB0 : B = 0
  . -- hB0 : B = 0
    subst hB0
    -- hB : ∀ (n : ℕ), |u n| ≤ 0
    -- hBnoneg : 0 ≤ 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    use 0
    -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(u * v) n - 0| < ε
    intros n _hn
    -- n : ℕ
    -- hn : n ≥ 0
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n * v n|   := congr_arg abs (Pi.mul_apply u v n)
       _ = |u n| * |v n| := abs_mul (u n) (v n)
       _ ≤ 0 * |v n|     := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
       _ = 0             := zero_mul (|v n|)
       _ < ε             := hε
  . -- hB0 : ¬B = 0
    change B ≠ 0 at hB0
    -- hB0 : B ≠ 0
    have hBpos : 0 < B := (Ne.le_iff_lt hB0.symm).mp hBnoneg
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    cases' hV (ε/B) (div_pos hε hBpos) with k hk
    -- k : ℕ
    -- hk : ∀ (n : ℕ), n ≥ k → |v n - 0| < ε / B
    use k
    -- ⊢ ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n * v n|    := congr_arg abs (Pi.mul_apply u v n)
       _ = |u n| * |v n|  := abs_mul (u n) (v n)
       _ ≤ B * |v n|      := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
       _ < B * (ε/B)      := mul_lt_mul_of_pos_left (hk n hn) hBpos
       _ = ε              := mul_div_cancel' ε hB0

-- 2ª demostración
-- ===============

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
by
  cases' hU with B hB
  -- B : ℝ
  -- hB : ∀ (n : ℕ), |u n| ≤ B
  have hBnoneg : 0 ≤ B :=
    calc 0 ≤ |u 0| := abs_nonneg (u 0)
         _ ≤ B     := hB 0
  by_cases hB0 : B = 0
  . subst hB0
    -- hB : ∀ (n : ℕ), |u n| ≤ 0
    -- hBnoneg : 0 ≤ 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    use 0
    -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(u * v) n - 0| < ε
    intros n _hn
    -- n : ℕ
    -- _hn : n ≥ 0
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n| * |v n| := by aesop
       _ ≤ 0 * |v n|     := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
       _ = 0             := by ring
       _ < ε             := hε
  . -- hB0 : ¬B = 0
    change B ≠ 0 at hB0
    -- hB0 : B ≠ 0
    have hBpos : 0 < B := (Ne.le_iff_lt hB0.symm).mp hBnoneg
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    cases' hV (ε/B) (div_pos hε hBpos) with k hk
    -- k : ℕ
    -- hk : ∀ (n : ℕ), n ≥ k → |v n - 0| < ε / B
    use k
    -- ∀ (n : ℕ), n ≥ k → |(u * v) n - 0| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |(u * v) n - 0| < ε
    simp_rw [sub_zero] at *
    -- ⊢ |(u * v) n| < ε
    calc |(u * v) n|
         = |u n| * |v n|  := by simp [Pi.mul_apply, abs_mul]
       _ ≤ B * |v n|      := mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
       _ < B * (ε/B)      := by aesop
       _ = ε              := mul_div_cancel' ε hB0

-- Lemas usados
-- ============

-- #variable (n : ℕ)
-- #variable (a b c : ℝ)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (Ne.le_iff_lt : a ≠ b → (a ≤ b ↔ a < b))
-- #check (Pi.mul_apply u v n : (u * v) n = u n * v n)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (mul_div_cancel' a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
-- #check (mul_lt_mul_of_pos_left : b < c → 0 < a → a * b < a * c)
-- #check (sub_zero a : a - 0 = a)
-- #check (zero_mul a : 0 * a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

definition acotada :: "(nat ⇒ real) ⇒ bool"
  where "acotada u ⟷ (∃B. ∀n. ¦u n¦ ≤ B)"

lemma
  assumes "acotada u"
          "limite v 0"
  shows   "limite (λn. u n * v n) 0"
proof -
  obtain B where hB : "∀n. ¦u n¦ ≤ B"
    using assms(1) acotada_def by auto
  then have hBnoneg : "0 ≤ B" by auto
  show "limite (λn. u n * v n) 0"
  proof (cases "B = 0")
    assume "B = 0"
    show "limite (λn. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix ε :: real
      assume "0 < ε"
      have "∀n≥0. ¦u n * v n - 0¦ < ε"
      proof (intro allI impI)
        fix n :: nat
        assume "n ≥ 0"
        show "¦u n * v n - 0¦ < ε"
          using ‹0 < ε› ‹B = 0› hB by auto
      qed
      then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
        by (rule exI)
    qed
  next
    assume "B ≠ 0"
    then have hBpos : "0 < B"
      using hBnoneg by auto
    show "limite (λn. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix ε :: real
      assume "0 < ε"
      then have "0 < ε/B"
        by (simp add: hBpos)
      then obtain N where hN : "∀n≥N. ¦v n - 0¦ < ε/B"
        using assms(2) limite_def by auto
      have "∀n≥N. ¦u n * v n - 0¦ < ε"
      proof (intro allI impI)
        fix n :: nat
        assume "n ≥ N"
        have "¦v n¦ < ε/B"
          using ‹N ≤ n› hN by auto
        have "¦u n * v n - 0¦ = ¦u n¦ * ¦v n¦"
          by (simp add: abs_mult)
        also have "… ≤ B * ¦v n¦"
          by (simp add: hB mult_right_mono)
        also have "… < B * (ε/B)"
          using ‹¦v n¦ < ε/B› hBpos
          by (simp only: mult_strict_left_mono)
        also have "… = ε"
          using ‹B ≠ 0› by simp
        finally show "¦u n * v n - 0¦ < ε"
          by this
      qed
      then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
        by (rule exI)
    qed
  qed
qed

end
</pre>
