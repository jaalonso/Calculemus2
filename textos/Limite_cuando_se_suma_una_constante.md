---
Título: Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de uₙ+c es a+c
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si el límite de la sucesión \\(uₙ\\) es \\(a\\) y \\(c ∈ ℝ\\), entonces el límite de \\(uₙ+c\\) es \\(a+c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable {u : ℕ → ℝ}
variable {a c : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε ∈ ℝ\\) tal que \\(ε > 0\\). Tenemos que demostrar que
\\[ (∃ N)(∀ n ≥ N)[|(u(n) + c) - (a + c)| < ε] \\tag{1} \\]
Puesto que el límite de la sucesión \\(u\\) es \\(a\\), existe un \\(k\\) tal que
\\[ (∀ n ≥ k)[|u(n) - a| < ε] \\tag{2} \\]
Veamos que con k se verifica (1); es decir, que
\\[ (∀ n ≥ k)[|(u(n) + c) - (a + c)| < ε] \\]
Sea \\(n ≥ k\\). Entonces, por (2),
\\[ |u(n) - a| < ε \\tag{3} \\]
y, por consiguiente,
\\begin{align}
   |(u(n) + c) - (a + c)| &= |u(n) - a|   \\\\
                          &< ε            &&\\text{[por (3)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
variable {u : ℕ → ℝ}
variable {a c : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i + c) n - (a + c)| < ε
  dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n + c - (a + c)| < ε
  cases' h ε hε with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n + c - (a + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  calc |u n + c - (a + c)|
       = |u n - a|         := by norm_num
     _ < ε                 := hk n hn

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i + c) n - (a + c)| < ε
  dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n + c - (a + c)| < ε
  cases' h ε hε with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n + c - (a + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n + c - (a + c)| < ε
  convert hk n hn using 2
  -- ⊢ u n + c - (a + c) = u n - a
  ring

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
by
  intros ε hε
  dsimp
  convert h ε hε using 6
  ring

-- 4ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun i ↦ u i + c) (a + c) :=
  fun ε hε ↦ (by convert h ε hε using 6; ring)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limite_cuando_se_suma_una_constante.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Limite_cuando_se_suma_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
  shows   "limite (λ i.  u i + c)  (a + c)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦(u n + c) - (a + c)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "∃k. ∀n≥k. ¦u n - a¦ < ε"
      using assms limite_def by simp
    then obtain k where "∀n≥k. ¦u n - a¦ < ε"
      by (rule exE)
    then have "∀n≥k. ¦(u n + c) - (a + c)¦ < ε"
      by simp
    then show "∃k. ∀n≥k. ¦(u n + c) - (a + c)¦ < ε"
      by (rule exI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
  shows   "limite (λ i.  u i + c)  (a + c)"
  using assms limite_def
  by simp

end
</pre>
