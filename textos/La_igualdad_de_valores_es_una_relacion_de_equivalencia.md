---
title: La igualdad de valores es una relación de equivalencia
date: 2024-06-26 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Sean \\(X\\) e \\(Y\\) dos conjuntos y \\(f\\) una función de \\(X\\) en \\(Y\\). Se define la relación \\(\\mathrel{\\text{R}}\\) en \\(X\\) de forma que \\(x\\) está relacionado con \\(y\\) si \\(f(x) = f(y)\\).

Demostrar con Lean4 que \\(\\mathrel{\\text{R}}\\) es una relación de equivalencia.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {X Y : Type _}
variable (f : X → Y)

def R (x y : X) :=
  f x = f y

example : Equivalence (R f) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que \\(\\mathrel{\\text{R}}\\) es reflexiva, simétrica y transitiva,

Para demostrar que \\(\\mathrel{\\text{R}}\\) es reflexiva, sea \\(x ∈ X\\). Entonces, \\(f(x) = f(x)\\) y, por tanto \\(x\\mathrel{\\text{R}}x\\).

Para demostrar que \\(\\mathrel{\\text{R}}\\) es simétrica, sean \\(x, y ∈ X\\) tales que \\(x\\mathrel{\\text{R}}y\\). Entonces, \\(f(x) = f(y)\\). Luego, \\(f(y) = f(x)\\) y, por tanto, \\(y\\mathrel{\\text{R}}x\\).

Para demostrar que \\(\\mathrel{\\text{R}}\\) es transitiva, sean \\(x, y, z ∈ X\\) tales que \\(x\\mathrel{\\text{R}}y\\) y \\(y\\mathrel{\\text{R}}z\\). Entonces, \\(f(x) = f(y)\\) y \\(f(y) = f(z)\\). Luego, \\(f(x) = f(z)\\) y, por tanto, \\(z\\mathrel{\\text{R}}z\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X Y : Type _}
variable (f : X → Y)

def R (x y : X) :=
  f x = f y

-- 1ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    intro x
    -- x : X
    -- ⊢ R f x x
    unfold R
    -- ⊢ f x = f x
    exact Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    intros x y hxy
    -- x y : X
    -- hxy : R f x y
    -- ⊢ R f y x
    unfold R at *
    -- hxy : f x = f y
    -- ⊢ f y = f x
    exact Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    intros x y z hxy hyz
    -- x y z : X
    -- hxy : R f x y
    -- hyz : R f y z
    -- ⊢ R f x z
    unfold R at *
    -- hxy : f x = f y
    -- hyz : f y = f z
    -- ⊢ f x = f z
    exact Eq.trans hxy hyz

-- 2ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    intro x
    -- x : X
    -- ⊢ R f x x
    exact Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    intros x y hxy
    -- x y : X
    -- hxy : R f x y
    -- ⊢ R f y x
    exact Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    intros x y z hxy hyz
    -- x y z : X
    -- hxy : R f x y
    -- hyz : R f y z
    -- ⊢ R f x z
    exact Eq.trans hxy hyz

-- 3ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    exact fun x ↦ Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    exact fun hxy ↦ Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    exact fun hxy hyz ↦ by exact  Eq.trans hxy hyz

-- 4ª demostración
-- ===============

example : Equivalence (R f) :=
⟨fun x ↦ Eq.refl (f x),
 fun hxy ↦ Eq.symm hxy,
 fun hxy hyz ↦ Eq.trans hxy hyz⟩

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.refl x : x = x)
-- #check (Eq.symm : x = y → y = x)
-- #check (Eq.trans : x = y → y = z → x = z)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_igualdad_de_valores_es_una_relacion_de_equivalencia.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_igualdad_de_valores_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "('a ⇒ 'b) ⇒ 'a ⇒ 'a ⇒ bool" where
  "R f x y ⟷ (f x = f y)"

(* 1ª demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    have "f x = f x"
      by (rule refl)
    then show "R f x x"
      by (unfold R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then have "f x = f y"
      by (unfold R_def)
    then have "f y = f x"
      by (rule sym)
    then show "R f y x"
      by (unfold R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then have "f x = f y" and "f y = f z"
      by (unfold R_def)
    then have "f x = f z"
      by (rule ssubst)
    then show "R f x z"
      by (unfold R_def)
  qed
qed

(* 2ª demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    show "R f x x"
      by (metis R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then show "R f y x"
      by (metis R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then show "R f x z"
      by (metis R_def)
  qed
qed

(* 3ª demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
    by (simp add: R_def reflpI)
next
  show "symp (R f)"
    by (metis R_def sympI)
next
  show "transp (R f)"
    by (metis R_def transpI)
qed

(* 4ª demostración *)

lemma "equivp (R f)"
  by (metis R_def
            equivpI
            reflpI
            sympI
            transpI)

end
</pre>
