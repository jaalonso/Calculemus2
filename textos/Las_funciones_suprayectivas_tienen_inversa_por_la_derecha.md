---
title: Las funciones suprayectivas tienen inversa por la derecha
date: 2024-06-13 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4, que \\(g\\) es una inversa por la izquierda de \\(f\\) está definido por
<pre lang="lean">
   LeftInverse (g : β → α) (f : α → β) : Prop :=
      ∀ x, g (f x) = x
</pre>
que \\(g\\) es una inversa por la derecha de \\(f\\) está definido por
<pre lang="lean">
   RightInverse (g : β → α) (f : α → β) : Prop :=
      LeftInverse f g
</pre>
y que \\(f\\) tenga inversa por la derecha está definido por
<pre lang="lean">
   HasRightInverse (f : α → β) : Prop :=
      ∃ g : β → α, RightInverse g f
</pre>
Finalmente, que \\(f\\) es suprayectiva está definido por
<pre lang="lean">
   def Surjective (f : α → β) : Prop :=
      ∀ b, ∃ a, f a = b
</pre>

Demostrar con Lean4 que si \\(f\\) es una función suprayectiva, entonces \\(f\\) tiene inversa por la derecha.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function Classical

variable {α β: Type _}
variable {f : α → β}

example
  (hf : Surjective f)
  : HasRightInverse f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(f: A → B\) una función suprayectiva. Sea \(g: B → A\) la función definida por
\[ g(y) = x, \text{donde \(x\) es un elemento tal que \(f(x) = y\) \]

Veamos que \(g\) es una inversa por la derecha de \(f\); es decir,
\[ (∀y ∈ B)[f(g(y)) = y \]
Para ello, sea \(b ∈ B\). Entonces,
\[ f(g(b)) = f(a) \]
donde \(a\) es un elemento tal que
\[ f(a) = b \]
Por tanto,
\[ f(g(b)) = b \]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function Classical

variable {α β: Type _}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  unfold HasRightInverse
  -- ⊢ ∃ finv, Function.RightInverse finv f
  let g := fun y ↦ Classical.choose (hf y)
  use g
  -- ⊢ Function.RightInverse g f
  unfold Function.RightInverse
  -- ⊢ LeftInverse f g
  unfold Function.LeftInverse
  -- ⊢ ∀ (x : β), f (g x) = x
  intro b
  -- ⊢ f (g b) = b
  exact Classical.choose_spec (hf b)

-- 2ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  let g := fun y ↦ Classical.choose (hf y)
  use g
  -- ⊢ Function.RightInverse g f
  intro b
  -- ⊢ f (g b) = b
  exact Classical.choose_spec (hf b)

-- 3ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  use surjInv hf
  -- ⊢ Function.RightInverse (surjInv hf) f
  intro b
  -- ⊢ f (surjInv hf b) = b
  exact surjInv_eq hf b

-- 4ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  use surjInv hf
  -- ⊢ Function.RightInverse (surjInv hf) f
  exact surjInv_eq hf

-- 5ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
⟨surjInv hf, surjInv_eq hf⟩

-- 6ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
⟨_, rightInverse_surjInv hf⟩

-- 7ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
Surjective.hasRightInverse hf

-- Lemas usados
-- ============

-- variable (p : α -> Prop)
-- #check (Classical.choose_spec : (h : ∃ x, p x) → p (Classical.choose h))
--
-- variable (h : Surjective f)
-- variable (b : β)
-- #check (surjInv_eq h b : f (surjInv h b) = b)
-- #check (rightInverse_surjInv h : RightInverse (surjInv h) f)
--
-- #check (Surjective.hasRightInverse : Surjective f → HasRightInverse f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_suprayectivas_tienen_inversa_por_la_derecha
imports Main
begin

definition tiene_inversa_dcha :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_dcha f ⟷ (∃g. ∀y. f (g y) = y)"

(* 1ª demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "λy. SOME x. f x = y"
  have "∀y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "∃x. y = f x"
      using assms by (rule surjD)
    then have "∃x. f x = y"
      by auto
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 2ª demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "λy. SOME x. f x = y"
  have "∀y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "∃x. f x = y"
      by (metis assms surjD)
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 3ª demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  have "∀y. f (inv f y) = y"
    by (simp add: assms surj_f_inv_f)
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 4ª demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
  by (metis assms surjD tiene_inversa_dcha_def)

end
</pre>
