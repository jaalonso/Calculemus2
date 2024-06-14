---
title: Las funciones con inversa son biyectivas
date: 2024-06-14 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4 se puede definir que \\(g\\) es una inversa de \\(f\\) por
<pre lang="lean">
   def inversa (f : X → Y) (g : Y → X) :=
     (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
</pre>
y que \\(f\\) tiene inversa por
<pre lang="lean">
   def tiene_inversa (f : X → Y) :=
     ∃ g, inversa g f
</pre>

Demostrar con Lean4 que si la función \\(f\\) tiene inversa, entonces \\(f\\) es biyectiva.

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
  (hf : tiene_inversa f)
  : Bijective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Puesto que \\(f: X → Y\\) tiene inversa, existe una \\(g: Y → X\\) tal que
\\begin{align}
   &(∀x)[(g ∘ f)(x) = x] \\tag{1} \\\\
   &(∀y)[(f ∘ g)(y) = y] \\tag{2}
\\end{align}

Para demostrar que \\(f\\) es inyectiva, sean \\(a, b ∈ X\\) tales que
\\[ f(a) = f(b) \\tag{3} \\]
entonces
\\begin{align}
   a &= g(f(a))    &&\\text{[por (1)]} \\\\
     &= g(f(b))    &&\\text{[por (3)]} \\\\
     &= b          &&\\text{[por (1)]}
\\end{align}

Para demostrar que \\(f\\) es suprayectiva, sea \\(y ∈ Y\\). Entonces, existe \\(a = g(y) ∈ X\\) tal que
\\begin{align}
   f(a) &= f(g(y))    \\\\
        &= y          &&\\text{[por (2)]}
\\end{align}

Como \\(f\\) es inyectiva y suprayectiva, entonces \\(f\\) es biyectiva.

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
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  -- g : Y → X
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  constructor
  . -- ⊢ Injective f
    intros a b hab
    -- a b : X
    -- hab : f a = f b
    -- ⊢ a = b
    calc a = g (f a) := (h2 a).symm
         _ = g (f b) := congr_arg g hab
         _ = b       := h2 b
  . -- ⊢ Surjective f
    intro y
    -- y : Y
    -- ⊢ ∃ a, f a = y
    use g y
    -- ⊢ f (g y) = y
    exact h1 y

-- 2ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  -- g : Y → X
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  constructor
  . -- ⊢ Injective f
    intros a b hab
    -- a b : X
    -- hab : f a = f b
    -- ⊢ a = b
    calc a = g (f a) := (h2 a).symm
         _ = g (f b) := congr_arg g hab
         _ = b       := h2 b
  . -- ⊢ Surjective f
    intro y
    -- y : Y
    -- ⊢ ∃ a, f a = y
    exact ⟨g y, h1 y⟩

-- 3ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  constructor
  . exact LeftInverse.injective h2
  . exact RightInverse.surjective h1

-- 4ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  exact ⟨LeftInverse.injective h2,
         RightInverse.surjective h1⟩

-- 5ª demostración
-- ===============

example :
  tiene_inversa f → Bijective f :=
by
  rintro ⟨g, ⟨h1, h2⟩⟩
  exact ⟨LeftInverse.injective h2,
         RightInverse.surjective h1⟩

-- 6ª demostración
-- ===============

example :
  tiene_inversa f → Bijective f :=
fun ⟨_, ⟨h1, h2⟩⟩ ↦ ⟨LeftInverse.injective h2,
                     RightInverse.surjective h1⟩

-- Lemas usados
-- ============

-- variable (x y : X)
-- variable (g : Y → X)
-- #check (congr_arg f : x = y → f x = f y)
-- #check (LeftInverse.injective : LeftInverse g f → Injective f)
-- #check (RightInverse.surjective : RightInverse g f → Surjective f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_con_inversa_son_biyectivas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_con_inversa_son_biyectivas
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

definition tiene_inversa :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa f ⟷ (∃ g. inversa f g)"

(* 1ª demostración *)

lemma
  fixes f :: "'a ⇒ 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                 h2 : "∀ y. (f ∘ g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

(* 2ª demostración *)

lemma
  fixes f :: "'a ⇒ 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                 h2 : "∀ y. (f ∘ g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

end
</pre>
