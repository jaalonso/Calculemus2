---
Título: Teorema del emparedado
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 el teorema del emparedado.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u v w : ℕ → ℝ)
variable (a : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para cada \\(ε > 0\\), existe un \\(N ∈ ℕ\\) tal que
\\[ (∀ n ≥ N)[|v(n) - a| ≤ ε] \\tag{1} \\]

Puesto que el límite de \\(u\\) es \\(a\\), existe un \\(U ∈ ℕ\\) tal que
\\[ (∀ n ≥ U)[|u(n) - a| ≤ ε] \\tag{2} \\]
y, puesto que el límite de \\(w\\) es \\(a\\), existe un \\(W ∈ ℕ\\) tal que
\\[ (∀ n ≥ W)[|w(n) - a| ≤ ε] \\tag{3} \\]
Sea \\(N = \\text{máx}(U, W)\\). Veamos que se verifica (1). Para ello, sea \\(n ≥ N\\). Entonces, \\(n ≥ U\\), \\(n ≥ W\\) y, por (2) y (3), se tiene que
\\begin{align}
    |u(n) - a| &≤ ε \\tag{4} \\\\
    |w(n) - a| &≤ ε \\tag{5}
\\end{align}
Para demostrar que
\\[ |v(n) - a| ≤ ε \\]
basta demostrar las siguientes desigualdades
\\begin{align}
    &-ε ≤ v(n) - a \\tag{6} \\\\
    &v(n) - a ≤ ε  \\tag{7}
\\end{align}
La demostración de (6) es
\\begin{align}
   -ε &≤ u(n) - a    &&\\text{[por (4)]} \\\\
      &≤ v(n) - a    &&\\text{[por hipótesis]}
\\end{align}
La demostración de (7) es
\\begin{align}
   v(n) - a &≤ w(n) - a    &&\\text{[por hipótesis]} \\\\
            &≤ ε           &&\\text{[por (5)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u v w : ℕ → ℝ)
variable (a : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- Nota. En la demostración se usará el siguiente lema:
lemma max_ge_iff
  {p q r : ℕ}
  : r ≥ max p q ↔ r ≥ p ∧ r ≥ q :=
  max_le_iff

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  -- ⊢ |v n - a| ≤ ε
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n hn.1
  -- hU : |u n - a| ≤ ε
  specialize hW n hn.2
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  clear hn
  rw [abs_le] at *
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor
  . -- ⊢ -ε ≤ v n - a
    calc -ε
         ≤ u n - a := hU.1
       _ ≤ v n - a := by linarith
  . -- ⊢ v n - a ≤ ε
    calc v n - a
         ≤ w n - a := by linarith
       _ ≤ ε       := hW.2

-- 2ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n (by linarith)
  -- hU : |u n - a| ≤ ε
  specialize hW n (by linarith)
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  rw [abs_le] at *
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor
  . -- ⊢ -ε ≤ v n - a
    linarith
  . -- ⊢ v n - a ≤ ε
    linarith

-- 3ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  -- ⊢ |v n - a| ≤ ε
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n (by linarith)
  -- hU : |u n - a| ≤ ε
  specialize hW n (by linarith)
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  rw [abs_le] at *
  -- hU : -ε ≤ u n - a ∧ u n - a ≤ ε
  -- hW : -ε ≤ w n - a ∧ w n - a ≤ ε
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor <;> linarith
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Teorema_del_emparedado.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Teorema_del_emparedado
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u a"
          "limite w a"
          "∀n. u n ≤ v n"
          "∀n. v n ≤ w n"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume hε : "0 < ε"
  obtain N where hN : "∀n≥N. ¦u n - a¦ < ε"
    using assms(1) hε limite_def
    by auto
  obtain N' where hN' : "∀n≥N'. ¦w n - a¦ < ε"
    using assms(2) hε limite_def
    by auto
  have "∀n≥max N N'. ¦v n - a¦ < ε"
  proof (intro allI impI)
    fix n
    assume hn : "n≥max N N'"
    have "v n - a < ε"
    proof -
      have "v n - a ≤ w n - a"
        using assms(4) by simp
      also have "… ≤ ¦w n - a¦"
        by simp
      also have "… < ε"
        using hN' hn by auto
      finally show "v n - a < ε" .
    qed
    moreover
    have "-(v n - a) < ε"
    proof -
      have "-(v n - a) ≤ -(u n - a)"
        using assms(3) by auto
      also have "… ≤ ¦u n - a¦"
        by simp
      also have "… < ε"
        using hN hn by auto
      finally show "-(v n - a) < ε" .
    qed
    ultimately show "¦v n - a¦ < ε"
      by (simp only: abs_less_iff)
  qed
  then show "∃k. ∀n≥k. ¦v n - a¦ < ε"
    by (rule exI)
qed

end
</pre>
