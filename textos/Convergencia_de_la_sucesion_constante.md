---
Título: La sucesión constante sₙ = c converge a c
Autor:  José A. Alonso
---

[mathjax]

En Lean, una sucesión \\(s₀, s₁, s₂, ...\\) se puede representar mediante una función \\((s : ℕ → ℝ)\\) de forma que \\(s(n)\\) es \\(sₙ\\).

Se define que a es el límite de la sucesión \\(s\\), por
<pre lang="text">
def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
</pre>

Demostrar que el límite de la sucesión constante \\(sₙ = c\\) es \\(c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : limite (fun _ : ℕ ↦ c) c :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para cada \\(ε ∈ ℝ\\) tal que \\(ε > 0\\), existe un \\(N ∈ ℕ\\), tal que \\((∀n ∈ ℕ)[n ≥ N → |s(n) - a| < ε]\\). Basta tomar \\(N\\) como \\(0\\), ya que para todo \\(n ≥ N\\) se tiene
\\begin{align}
   |s(n) - a| &= |a - a| \\\\
              &= |0|     \\\\
              &= 0       \\\\
              &< ε       \\\\
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- 1ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun _ => c) n - c| < ε
  intros n _hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |(fun _ => c) n - c| < ε
  show |(fun _ => c) n - c| < ε
  calc |(fun _ => c) n - c| = |c - c| := by dsimp
                          _ = |0|     := by {congr ; exact sub_self c}
                          _ = 0       := abs_zero
                          _ < ε       := hε

-- 2ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |(fun _ => c) n - c| < ε
  intros n _hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |(fun _ => c) n - c| < ε
  show |(fun _ => c) n - c| < ε
  calc |(fun _ => c) n - c| = 0       := by simp
                          _ < ε       := hε

-- 3ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  aesop

-- 4ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun _ => c) n - c| < ε
  aesop

-- 5ª demostración
-- ===============

example : limite (fun _ : ℕ ↦ c) c :=
  fun ε hε ↦ by aesop

-- Lemas usados
-- ============

-- #check (sub_self a : a - a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Convergencia_de_la_sucesion_constante.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Limite_de_sucesiones_constantes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma "limite (λ n. c) c"
proof (unfold limite_def)
  show "∀ε>0. ∃k::nat. ∀n≥k. ¦c - c¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    have "∀n≥0::nat. ¦c - c¦ < ε"
    proof (intro allI impI)
      fix n :: nat
      assume "0 ≤ n"
      have "c - c = 0"
        by (simp only: diff_self)
      then have "¦c - c¦ = 0"
        by (simp only: abs_eq_0_iff)
      also have "… < ε"
        by (simp only: ‹0 < ε›)
      finally show "¦c - c¦ < ε"
        by this
    qed
    then show "∃k::nat. ∀n≥k. ¦c - c¦ < ε"
      by (rule exI)
  qed
qed

(* 2ª demostración *)

lemma "limite (λ n. c) c"
proof (unfold limite_def)
  show "∀ε>0. ∃k::nat. ∀n≥k. ¦c - c¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    have "∀n≥0::nat. ¦c - c¦ < ε"          by (simp add: ‹0 < ε›)
    then show "∃k::nat. ∀n≥k. ¦c - c¦ < ε" by (rule exI)
  qed
qed

(* 3ª demostración *)

lemma "limite (λ n. c) c"
  unfolding limite_def
  by simp

(* 4ª demostración *)

lemma "limite (λ n. c) c"
  by (simp add: limite_def)

end
</pre>

<h2>Referencias</h2>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 41.</li>
</ul>
