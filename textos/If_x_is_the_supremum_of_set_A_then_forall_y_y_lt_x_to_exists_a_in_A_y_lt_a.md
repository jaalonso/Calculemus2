---
title: If x is the supremum of set A, then ((∀ y)[y < x → (∃ a ∈ A)[y < a]]
date: 2024-08-31 06:00:00 UTC+02:00
category: Real numbers
has_math: true
---

[mathjax]

In Lean4, one can define that \(x\) is an upper bound of \(A\) by
<pre lang="lean">
   def is_upper_bound (A : Set ℝ) (x : ℝ) :=
     ∀ a ∈ A, a ≤ x
</pre>
and \(x\) is supremum of \(A\) by
<pre lang="lean">
   def is_supremum (A : Set ℝ) (x : ℝ) :=
     is_upper_bound A x ∧ ∀ y, is_upper_bound A y → x ≤ y
</pre>

Prove that if \(x\) is the supremum of \(A\), then
\[ (∀ y)[y < x → (∃ a ∈ A)[y < a]] \]

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {A : Set ℝ}
variable {x : ℝ}

def is_upper_bound (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def is_supremum (A : Set ℝ) (x : ℝ) :=
  is_upper_bound A x ∧ ∀ y, is_upper_bound A y → x ≤ y

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Suppose \(y < x\). Assume for contradiction that
\[ (∀ a ∈ A)[a ≤ y] \]
Then \(y\) is an upper bound of \(A\), but \(x\) is the supremum, so \(x ≤ y\), contradicting \(y < x\).

Therefore,
\[ (∃ a ∈ A)[y < a] \]

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {A : Set ℝ}
variable {x : ℝ}

def is_upper_bound (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def is_supremum (A : Set ℝ) (x : ℝ) :=
  is_upper_bound A x ∧ ∀ y, is_upper_bound A y → x ≤ y

-- Proof 1
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : is_upper_bound A y := h
  have h2 : x ≤ y := hx.2 y h1
  have h3 : ¬x ≤ y := not_le.mpr hy
  exact h3 h2

-- Proof 2
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : x ≤ y := hx.2 y h
  replace h1 : ¬(y < x) := not_lt_of_le h1
  exact h1 hy

-- Proof 3
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  apply absurd hy
  -- ⊢ ¬y < x
  apply not_lt_of_le
  -- ⊢ x ≤ y
  apply hx.2 y
  -- ⊢ is_upper_bound A y
  exact h

-- Proof 4
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  exact absurd hy (not_lt_of_le (hx.2 y h))

-- Proof 5
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  unfold is_supremum at hx
  -- hx : is_upper_bound A x ∧ ∀ (y : ℝ), is_upper_bound A y → x ≤ y
  rcases hx with ⟨_, h2⟩
  -- h2 : ∀ (y : ℝ), is_upper_bound A y → x ≤ y
  apply h2 y
  -- h2 : ∀ (y : ℝ), is_upper_bound A y → x ≤ y
  unfold is_upper_bound
  -- ⊢ ∀ a ∈ A, a ≤ y
  exact hy

-- Proof 6
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  rcases hx with ⟨-, h2⟩
  -- h2 : ∀ (y : ℝ), is_upper_bound A y → x ≤ y
  exact h2 y hy

-- Proof 7
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  exact hx.right y hy

-- Proof 8
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y
  -- y : ℝ
  -- ⊢ y < x → ∃ a ∈ A, y < a
  contrapose!
  -- ⊢ (∀ a ∈ A, a ≤ y) → x ≤ y
  exact hx.right y

-- Proof 9
-- =======

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  exact (lt_isLUB_iff hx).mp hy

-- Proof 10
-- ========

example
  (hx : is_supremum A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
fun _ hy ↦ (lt_isLUB_iff hx).mp hy

-- Used lemmas
-- ===========

-- variable (a b c : ℝ)
-- variable (p q : Prop)
-- #check (absurd : p → ¬p → q)
-- #check (lt_isLUB_iff : IsLUB A a → (b < a ↔ ∃ c ∈ A, b < c))
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (not_lt_of_le : a ≤ b → ¬b < a)
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/If_x_is_the_supremum_of_set_A_then_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory "If_x_is_the_supremum_of_set_A_then_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a"
  imports Main HOL.Real
begin

definition is_upper_bound :: "(real set) ⇒ real ⇒ bool" where
  "is_upper_bound A x ⟷ (∀a∈A. a ≤ x)"

definition is_supremum :: "(real set) ⇒ real ⇒ bool" where
  "is_supremum A x ⟷ (is_upper_bound A x ∧
                       (∀ y. is_upper_bound A y ⟶ x ≤ y))"

(* Proof 1 *)
lemma
  assumes "is_supremum A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "∀a∈A. a ≤ y"
      by auto
    then have "is_upper_bound A y"
      using is_upper_bound_def by simp
    then have "x ≤ y"
      using assms is_supremum_def by simp
    then have "x < x"
      using ‹y < x› by simp
    then show False by simp
  qed
qed

(* Proof 2 *)
lemma
  assumes "is_supremum A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "is_upper_bound A y"
      using is_upper_bound_def by auto
    then show "False"
      using assms is_supremum_def ‹y < x› by auto
  qed
qed

end
</pre>
