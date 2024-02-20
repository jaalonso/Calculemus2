---
Título: Si uₙ y vₙ convergen a 0, entonces uₙvₙ converge a 0
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(uₙ\\) y \\(vₙ\\) convergen a \\(0\\), entonces \\(uₙvₙ\\) converge a \\(0).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε ∈ ℝ\\) tal que \\(ε > 0\\). Tenemos que demostrar que
\\[ (∃N ∈ ℕ)(∀n ≥ N)[|(u·v)(n) - 0| < ε] \\tag{1} \\]
Puesto que el límite de \\(uₙ\\) es \\(0\\), existe un \\(U ∈ ℕ\\) tal que
\\[ (∀n ≥ U)[|u(n) - 0| < ε] \\tag{2} \\]
y, puesto que el límite de \\(vₙ\\) es \\(0\\), existe un \\(V ∈ ℕ\\) tal que
\\[ (∀n ≥ V)[|v(n) - 0| < 1] \\tag{3} \\]
Entonces, \\(N = \\text{máx}(U, V)\\) cumple (1). En efecto, sea \\(n ≥ N\\). Entonces,
\\(n ≥ U\\) y \\(n ≥ V\\) y, aplicando (2) y (3), se tiene
\\begin{align}
   &|u(n) - 0| < ε \\tag{4} \\\\
   &|v(n) - 0| < 1 \\tag{5}
\\end{align}
Por tanto,
\\begin{align}
   |(u·v)(n) - 0| &= |u(n)·v(n)|     \\\\
                  &= |u(n)|·|v n|    \\\\
                  &< ε·1             &&\\text{[por (4) y (5)]} \\\\
                  &= ε
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 zero_lt_one with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n - 0| < ε
  -- hV : |v n - 0| < 1
  -- ⊢ |(u * v) n - 0| < ε
  calc |(u * v) n|
       = |u n * v n|   := rfl
     _ = |u n| * |v n| := abs_mul (u n) (v n)
     _ < ε * 1         := mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
     _ = ε             := mul_one ε

-- 2ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 (by linarith) with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n| < ε
  -- hV : |v n| < 1
  -- ⊢ |(u * v) n| < ε
  calc |(u * v) n|
       = |u n * v n|   := rfl
     _ = |u n| * |v n| := abs_mul (u n) (v n)
     _ < ε * 1         := by { apply mul_lt_mul'' hU hV <;> simp [abs_nonneg] }
     _ = ε             := mul_one ε

-- 3ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  cases' hu ε hε with U hU
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  cases' hv 1 (by linarith) with V hV
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  have hUN : U ≤ N := le_max_left U V
  have hVN : V ≤ N := le_max_right U V
  specialize hU n (by linarith)
  -- hU : |u n - 0| < ε
  specialize hV n (by linarith)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n| < ε
  -- hV : |v n| < 1
  -- ⊢ |(u * v) n| < ε
  rw [Pi.mul_apply]
  -- ⊢ |u n * v n| < ε
  rw [abs_mul]
  -- ⊢ |u n| * |v n| < ε
  convert mul_lt_mul'' hU hV _ _ using 2 <;> simp

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- variable (I : Type _)
-- variable (f : I → Type _)
-- #check (zero_lt_one : 0 < 1)
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (sub_zero a : a - 0 = a)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (mul_one a : a * 1 = a)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_sucesiones_convergentes_a_cero.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Producto_de_sucesiones_convergentes_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u 0"
          "limite v 0"
  shows   "limite (λ n. u n * v n) 0"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume  hε : "0 < ε"
  then obtain U where hU : "∀n≥U. ¦u n - 0¦ < ε"
    using assms(1) limite_def
    by auto
  obtain V where hV : "∀n≥V. ¦v n - 0¦ < 1"
    using hε assms(2) limite_def
    by fastforce
  have "∀n≥max U V. ¦u n * v n - 0¦ < ε"
  proof (intro allI impI)
    fix n
    assume hn : "max U V ≤ n"
    then have "U ≤ n"
      by simp
    then have "¦u n - 0¦ < ε"
      using hU by blast
    have hnV : "V ≤ n"
      using hn by simp
    then have "¦v n - 0¦ < 1"
      using hV by blast
    have "¦u n * v n - 0¦ = ¦(u n - 0) * (v n - 0)¦"
      by simp
    also have "… = ¦u n - 0¦ * ¦v n - 0¦"
      by (simp add: abs_mult)
    also have "… < ε * 1"
      using ‹¦u n - 0¦ < ε› ‹¦v n - 0¦ < 1›
      by (rule abs_mult_less)
    also have "… = ε"
      by simp
    finally show "¦u n * v n - 0¦ < ε"
      by this
  qed
  then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
    by (rule exI)
qed

end
</pre>
