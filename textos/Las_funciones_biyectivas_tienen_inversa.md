---
title: Las funciones biyectivas tienen inversa
date: 2024-06-17 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4 se puede definir que \(g\) es una inversa de \(f\) por
<pre lang="haskell">
   def inversa (f : X → Y) (g : Y → X) :=
     (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
</pre>
y que \(f\) tiene inversa por
<pre lang="haskell">
   def tiene_inversa (f : X → Y) :=
     ∃ g, inversa f g
</pre>

Demostrar con Lean4 que si la función \(f\) es biyectiva, entonces \(f\) tiene inversa.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

example
  (hf : Bijective f)
  : tiene_inversa f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(f: X → Y\) biyectiva. Entonces, \(f\) es suprayectiva y se puede definir la función \(g: Y → X\) tal que
\[ g(y) = x, \text{donde \(x\) es un elemento de \(X\) tal que \(f(x) = y\) \]
Por tanto,
\[ (∀y ∈ Y)[f(g(y)) = y] \tag{1} \]

Veamos que \(g\) es inversa de \(f\); es decir, que se verifican
\begin{align}
   &(∀y ∈ Y)[(f ∘ g) y = y] \tag{2} \\
   &(∀x ∈ X)[(g ∘ f) x = x] \tag{3}
\end{align}

La propiedad (2) se tiene por (1) y la definición de composición.

Para demostrar (3), sea \(x ∈ X\). Entonces, por (1),
\[ f(g(f(x))) = f(x) \]
y, por ser f inyectiva,
\[ g(f(x)) = x \]
Luego,
\[ (g ∘ f)(x) = x \]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

-- 1ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  constructor
  . -- ⊢ ∀ (x : Y), (f ∘ g) x = x
    exact hg
  . -- ⊢ ∀ (y : X), (g ∘ f) y = y
    intro a
    -- a : X
    -- ⊢ (g ∘ f) a = a
    rw [comp_apply]
    -- ⊢ g (f a) = a
    apply hfiny
    -- ⊢ f (g (f a)) = f a
    rw [hg (f a)]

-- 2ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
    -- hfiny : Injective f
    -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  constructor
  . -- ⊢ ∀ (x : Y), (f ∘ g) x = x
    exact hg
  . -- ⊢ ∀ (y : X), (g ∘ f) y = y
    intro a
    -- a : X
    -- ⊢ (g ∘ f) a = a
    exact @hfiny (g (f a)) a (hg (f a))

-- 3ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  exact ⟨hg, fun a ↦ @hfiny (g (f a)) a (hg (f a))⟩

-- 4ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  exact ⟨g, ⟨hg, fun a ↦ @hfiny (g (f a)) a (hg (f a))⟩⟩

-- 5ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  cases' (bijective_iff_has_inverse.mp hf) with g hg
  -- g : Y → X
  -- hg : LeftInverse g f ∧ Function.RightInverse g f
  aesop (add norm unfold [tiene_inversa, inversa])

-- Lemas usados
-- ============

-- variable (g : Y → X)
-- variable (x : X)
-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
-- #check (comp_apply : (g ∘ f) x = g (f x))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_biyectivas_tienen_inversa.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_biyectivas_tienen_inversa
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

definition tiene_inversa :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa f ⟷ (∃ g. inversa f g)"

(* 1ª demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "∀y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (g ∘ f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using ‹bij f› by (rule bij_is_inj)
      then show "(g ∘ f) x = x"
      proof (rule injD)
        have "f ((g ∘ f) x) = f (g (f x))"
          by simp
        also have "… = f x"
          by (simp add: hg)
        finally show "f ((g ∘ f) x) = f x"
          by this
      qed
    qed
    next
      show "∀y. (f ∘ g) y = y"
        by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by blast
qed

(* 2ª demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "∀y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (g ∘ f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using ‹bij f› by (rule bij_is_inj)
      then show "(g ∘ f) x = x"
      proof (rule injD)
        have "f ((g ∘ f) x) = f (g (f x))"
          by simp
        also have "… = f x"
          by (simp add: hg)
        finally show "f ((g ∘ f) x) = f x"
          by this
      qed
    qed
  next
    show "∀y. (f ∘ g) y = y"
      by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

(* 3ª demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "inversa f (inv f)"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (inv f ∘ f) x = x"
      by (simp add: ‹bij f› bij_is_inj)
  next
    show "∀y. (f ∘ inv f) y = y"
      by (simp add: ‹bij f› bij_is_surj surj_f_inv_f)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

end
</pre>
