[mathjax]

Demostrar con Lean4 que si \\(f\\) es inyectiva, entonces
\\[ f[s] ∩ f[t] ⊆ f[s ∩ t] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set Function

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ f[s] ∩ f[t]\\). Entonces, existen \\(x₁\\) y \\(x₂\\) tales que
\\begin{align}
   &x₁ ∈ s      \\tag{1} \\\\
   &f(x₁) = y   \\tag{2} \\\\
   &x₂ ∈ t      \\tag{3} \\\\
   &f(x₂) = y   \\tag{4}
\\end{align}
De (2) y (4) se tiene que
\\[ f(x₁) = f(x₂) \\]
y, por ser \\(f\\) inyectiva, se tiene que
\\[ x₁ = x₂ \\]
y, por (1), se tiene que
\\[ x₂ ∈ t \\]
y, por (3), se tiene que
\\[ x₂ ∈ s ∩ t \\]
Por tanto,
\\[ f(x₂) ∈ f[s ∩ t] \\]
y, por (4),
\\[ y ∈ f[s ∩ t] \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set Function

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

-- 1ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s ∩ f '' t
  -- ⊢ y ∈ f '' (s ∩ t)
  rcases hy with ⟨hy1, hy2⟩
  -- hy1 : y ∈ f '' s
  -- hy2 : y ∈ f '' t
  rcases hy1 with ⟨x1, hx1⟩
  -- x1 : α
  -- hx1 : x1 ∈ s ∧ f x1 = y
  rcases hx1 with ⟨x1s, fx1y⟩
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  rcases hy2 with ⟨x2, hx2⟩
  -- x2 : α
  -- hx2 : x2 ∈ t ∧ f x2 = y
  rcases hx2 with ⟨x2t, fx2y⟩
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  have h1 : f x1 = f x2 := Eq.trans fx1y fx2y.symm
  have h2 : x1 = x2 := h (congrArg f (h h1))
  have h3 : x2 ∈ s := by rwa [h2] at x1s
  have h4 : x2 ∈ s ∩ t := by exact ⟨h3, x2t⟩
  have h5 : f x2 ∈ f '' (s ∩ t) := mem_image_of_mem f h4
  show y ∈ f '' (s ∩ t)
  rwa [fx2y] at h5

-- 2ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s ∩ f '' t
  -- ⊢ y ∈ f '' (s ∩ t)
  rcases hy  with ⟨hy1, hy2⟩
  -- hy1 : y ∈ f '' s
  -- hy2 : y ∈ f '' t
  rcases hy1 with ⟨x1, hx1⟩
  -- x1 : α
  -- hx1 : x1 ∈ s ∧ f x1 = y
  rcases hx1 with ⟨x1s, fx1y⟩
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  rcases hy2 with ⟨x2, hx2⟩
  -- x2 : α
  -- hx2 : x2 ∈ t ∧ f x2 = y
  rcases hx2 with ⟨x2t, fx2y⟩
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  use x1
  -- ⊢ x1 ∈ s ∩ t ∧ f x1 = y
  constructor
  . -- ⊢ x1 ∈ s ∩ t
    constructor
    . -- ⊢ x1 ∈ s
      exact x1s
    . -- ⊢ x1 ∈ t
      convert x2t
      -- ⊢ x1 = x2
      apply h
      -- ⊢ f x1 = f x2
      rw [← fx2y] at fx1y
      -- fx1y : f x1 = f x2
      exact fx1y
  . -- ⊢ f x1 = y
    exact fx1y

-- 3ª demostración
-- ===============

example
  (h : Injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by
  rintro y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩
  -- y : β
  -- x1 : α
  -- x1s : x1 ∈ s
  -- fx1y : f x1 = y
  -- x2 : α
  -- x2t : x2 ∈ t
  -- fx2y : f x2 = y
  -- ⊢ y ∈ f '' (s ∩ t)
  use x1
  -- ⊢ x1 ∈ s ∩ t ∧ f x1 = y
  constructor
  . -- ⊢ x1 ∈ s ∩ t
    constructor
    . -- ⊢ x1 ∈ s
      exact x1s
    . -- ⊢ x1 ∈ t
      convert x2t
      -- ⊢ x1 = x2
      apply h
      -- ⊢ f x1 = f x2
      rw [← fx2y] at fx1y
      -- fx1y : f x1 = f x2
      exact fx1y
  . -- ⊢ f x1 = y
    exact fx1y
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_interseccion_de_aplicaciones_inyectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_interseccion_de_aplicaciones_inyectivas
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` s ∩ f ` t"
  then have "y ∈ f ` s"
    by (rule IntD1)
  then show "y ∈ f ` (s ∩ t)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s"
    have "x ∈ t"
    proof -
      have "y ∈ f ` t"
        using ‹y ∈ f ` s ∩ f ` t› by (rule IntD2)
      then show "x ∈ t"
      proof (rule imageE)
        fix z
        assume "y = f z"
        assume "z ∈ t"
        have "f x = f z"
          using ‹y = f x› ‹y = f z› by (rule subst)
        with ‹inj f› have "x = z"
          by (simp only: inj_eq)
        then show "x ∈ t"
          using ‹z ∈ t› by (rule ssubst)
      qed
    qed
    with ‹x ∈ s› have "x ∈ s ∩ t"
      by (rule IntI)
    with ‹y = f x› show "y ∈ f ` (s ∩ t)"
      by (rule image_eqI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
proof
  fix y
  assume "y ∈ f ` s ∩ f ` t"
  then have "y ∈ f ` s" by simp
  then show "y ∈ f ` (s ∩ t)"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s"
    have "x ∈ t"
    proof -
      have "y ∈ f ` t" using ‹y ∈ f ` s ∩ f ` t› by simp
      then show "x ∈ t"
      proof
        fix z
        assume "y = f z"
        assume "z ∈ t"
        have "f x = f z" using ‹y = f x› ‹y = f z› by simp
        with ‹inj f› have "x = z" by (simp only: inj_eq)
        then show "x ∈ t" using ‹z ∈ t› by simp
      qed
    qed
    with ‹x ∈ s› have "x ∈ s ∩ t" by simp
    with ‹y = f x› show "y ∈ f ` (s ∩ t)" by simp
  qed
qed

(* 3ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
  using assms
  by (simp only: image_Int)

(* 4ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
  using assms
  unfolding inj_def
  by auto

end
</pre>
