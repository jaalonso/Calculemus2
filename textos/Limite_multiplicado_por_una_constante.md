---
Título: Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de cuₙ es ca
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si el límite de la sucesión \\(uₙ\\) es \\(a\\) y \\(c ∈ ℝ\\), entonces el límite de \\(cuₙ\\) es \\(ca\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε ∈ ℝ\\) tal que \\(ε > 0\\). Tenemos que demostrar que
\\[ (∃ N ∈ ℕ)(∀ n ≥ N)[|cuₙ - ca| < ε] \\tag{1}\\]
Distinguiremos dos casos según sea \\(c = 0\\) o no.

Primer caso: Supongamos que \\(c = 0\\). Entonces, (1) se reduce a
\\[ (∃ N ∈ ℕ)(∀ n ≥ N)[|0·uₙ - 0·a| < ε] \\]
es decir,
\\[ (∃ N ∈ ℕ)(∀ n ≥ N)[0 < ε] \\]
que se verifica para cualquier número \\(N\\), ya que \\(ε > 0\\).

Segundo caso: Supongamos que \\(c ≠ 0\\). Entonces, \\(\\dfrac{ε}{|c|}\\) > 0 y, puesto que el límite de \\(uₙ\\) es \\(a\\), existe un \\(k ∈ ℕ\\) tal que
\\[ (∀ n ≥ k)[|uₙ - a| < \\frac{ε}{|c|}] \\tag{2} \\]
Veamos que con \\(k\\) se cumple (1). En efecto, sea \\(n ≥ k\\). Entonces,
\\begin{align}
   |cuₙ - ca| &= |c(uₙ - a)|    \\\\
              &= |c||uₙ - a|   \\\\
              &< |c|\\frac{ε}{|c|}     &&\\text{[por (2)]} \\\\
              &= ε
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    calc |c * u n - c * a|
         = |c * (u n - a)| := congr_arg abs (mul_sub c (u n) a).symm
       _ = |c| * |u n - a| := abs_mul c  (u n - a)
       _ < |c| * (ε / |c|) := (mul_lt_mul_left hc').mpr hN
       _ = ε               := mul_div_cancel' ε (ne_of_gt hc')

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    -- ⊢ |c * u n - c * a| < ε
    rw [← mul_sub]
    -- ⊢ |c * (u n - a)| < ε
    rw [abs_mul]
    -- ⊢ |c| * |u n - a| < ε
    rw [← lt_div_iff' hc']
    -- ⊢ |u n - a| < ε / |c|
    exact hN

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . subst hc
    intros ε hε
    aesop
  . intros ε hε
    have hc' : 0 < |c| := by aesop
    have hεc : 0 < ε / |c| := div_pos hε hc'
    cases' h (ε/|c|) hεc with N hN
    use N
    intros n hn
    specialize hN n hn
    dsimp only
    rw [← mul_sub, abs_mul, ← lt_div_iff' hc']
    exact hN

-- Lemas usados
-- ============

-- variable (b c : ℝ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b))
-- #check (mul_div_cancel' a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limite_multiplicado_por_una_constante.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Limite_multiplicado_por_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u a"
  shows   "limite (λ n. c * u n) (c * a)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
    proof (cases "c = 0")
      assume "c = 0"
      then show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
        by (simp add: ‹0 < ε›)
    next
      assume "c ≠ 0"
      then have "0 < ¦c¦"
        by simp
      then have "0 < ε/¦c¦"
        by (simp add: ‹0 < ε›)
      then obtain N where hN : "∀n≥N. ¦u n - a¦ < ε/¦c¦"
        using assms limite_def
        by auto
      have "∀n≥N. ¦c * u n - c * a¦ < ε"
      proof (intro allI impI)
        fix n
        assume "n ≥ N"
        have "¦c * u n - c * a¦ = ¦c * (u n - a)¦"
          by argo
        also have "… = ¦c¦ * ¦u n - a¦"
          by (simp only: abs_mult)
        also have "… < ¦c¦ * (ε/¦c¦)"
          using hN ‹n ≥ N› ‹0 < ¦c¦›
          by (simp only: mult_strict_left_mono)
        finally show "¦c * u n - c * a¦ < ε"
          using ‹0 < ¦c¦›
          by auto
      qed
      then show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
        by (rule exI)
    qed
  qed
qed

end
</pre>
